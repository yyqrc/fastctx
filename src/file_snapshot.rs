//! Stable, single-open byte snapshots for grep candidates.

use crate::binary::detect_binary_type;
use crate::encoding::{
    BomStreamingValidator, EncodingRejection, StrictStreamingValidator, Utf8ConflictProbe,
    bom_streaming_validator, explicit_streaming_validator,
};
use crate::operation::{WorkCheckpoint, WorkStop};
use crate::path_codec::{FileIdentityHint, PathRecord};
use std::fs::File;
use std::io::{self, BufReader, Cursor, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::Arc;

const PREFLIGHT_BYTES: usize = 8 * 1024;
const SNAPSHOT_CHUNK_BYTES: usize = 64 * 1024;
const MEMORY_SNAPSHOT_LIMIT: usize = 8 * 1024 * 1024;

/// A suffix-invariant reason that permits capture to stop before EOF.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TerminalProof {
    NulWithinFrozenProbe,
    BinaryMagicAfterUtf8Failure,
    ExplicitDecoderMalformed {
        encoding: String,
    },
    BomDecoderMalformed {
        encoding: &'static str,
    },
    AutomaticRejected {
        conflict_hex_offset: usize,
        fallback: FallbackTerminalState,
    },
}

/// Why no fallback decoder can overturn an automatic mixed-encoding proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FallbackTerminalState {
    Absent,
    PermanentlyMalformed,
}

impl TerminalProof {
    pub(crate) fn rejection(&self) -> Option<EncodingRejection> {
        match self {
            Self::NulWithinFrozenProbe | Self::BinaryMagicAfterUtf8Failure => None,
            Self::ExplicitDecoderMalformed { encoding } => {
                Some(EncodingRejection::ExplicitMalformed {
                    encoding: encoding.clone(),
                })
            }
            Self::BomDecoderMalformed { encoding } => {
                Some(EncodingRejection::BomMismatch { encoding })
            }
            Self::AutomaticRejected {
                conflict_hex_offset,
                ..
            } => Some(EncodingRejection::MixedOrInconsistent {
                conflict_hex_offset: Some(*conflict_hex_offset),
            }),
        }
    }
}

/// The stable result of capturing one candidate from its original handle.
pub(crate) enum CaptureDisposition {
    Searchable(Box<SealedSnapshot>),
    BinarySkipped(TerminalProof),
    EncodingRejected {
        rejection: EncodingRejection,
        proof: TerminalProof,
    },
    FileChanged,
}

/// Failures that must remain distinct from an actively changing candidate.
#[derive(Debug)]
pub(crate) enum CaptureFailure {
    Cancelled,
    EpochRetired,
    InvalidEncoding(EncodingRejection),
    Io(io::Error),
    Snapshot(io::Error),
}

/// A reader over one immutable snapshot backing.
pub(crate) enum SnapshotReader<'a> {
    Memory(Cursor<&'a [u8]>),
    Temp(BufReader<File>),
}

impl Read for SnapshotReader<'_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Memory(reader) => reader.read(output),
            Self::Temp(reader) => reader.read(output),
        }
    }
}

#[derive(Debug)]
struct TempSnapshot {
    file: tempfile::NamedTempFile,
}

impl TempSnapshot {
    fn open_reader(&self, start: u64) -> io::Result<SnapshotReader<'static>> {
        let mut file = self.file.reopen()?;
        if start > 0 {
            file.seek(SeekFrom::Start(start))?;
        }
        Ok(SnapshotReader::Temp(BufReader::new(file)))
    }
}

#[derive(Clone, Debug)]
enum SnapshotBacking {
    Memory(Arc<[u8]>),
    Temp(Arc<TempSnapshot>),
}

struct CapturedSnapshot {
    len: u64,
    backing: SnapshotBacking,
}

/// A cloneable immutable view used when decoded UTF-8 is the snapshot bytes themselves.
#[derive(Clone, Debug)]
pub(crate) struct SnapshotByteRange {
    backing: SnapshotBacking,
    start: u64,
    len: u64,
}

impl SnapshotByteRange {
    pub(crate) fn len(&self) -> u64 {
        self.len
    }

    pub(crate) fn memory_bytes(&self) -> Option<&[u8]> {
        let SnapshotBacking::Memory(bytes) = &self.backing else {
            return None;
        };
        let start = usize::try_from(self.start).ok()?;
        let length = usize::try_from(self.len).ok()?;
        let end = start.checked_add(length)?;
        bytes.get(start..end)
    }

    pub(crate) fn open_reader(&self) -> io::Result<SnapshotReader<'_>> {
        match &self.backing {
            SnapshotBacking::Memory(bytes) => {
                let start = usize::try_from(self.start).map_err(|_| snapshot_range_error())?;
                let length = usize::try_from(self.len).map_err(|_| snapshot_range_error())?;
                let end = start.checked_add(length).ok_or_else(snapshot_range_error)?;
                let bytes = bytes.get(start..end).ok_or_else(snapshot_range_error)?;
                Ok(SnapshotReader::Memory(Cursor::new(bytes)))
            }
            SnapshotBacking::Temp(snapshot) => snapshot.open_reader(self.start),
        }
    }

    pub(crate) fn read_range(&self, range: std::ops::Range<u64>) -> io::Result<Vec<u8>> {
        if range.start > range.end || range.end > self.len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "captured text range lies outside its snapshot backing",
            ));
        }
        let length = usize::try_from(range.end - range.start).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "captured text range does not fit in memory",
            )
        })?;
        let absolute_start = self.start.checked_add(range.start).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "snapshot offset overflow")
        })?;
        let mut reader = match &self.backing {
            SnapshotBacking::Memory(bytes) => {
                let start = usize::try_from(absolute_start).map_err(|_| {
                    io::Error::new(io::ErrorKind::InvalidData, "snapshot offset overflow")
                })?;
                let end = start.checked_add(length).ok_or_else(snapshot_range_error)?;
                let bytes = bytes.get(start..end).ok_or_else(snapshot_range_error)?;
                return Ok(bytes.to_vec());
            }
            SnapshotBacking::Temp(snapshot) => snapshot.open_reader(absolute_start)?,
        };
        let mut bytes = vec![0_u8; length];
        reader.read_exact(&mut bytes)?;
        Ok(bytes)
    }
}

fn snapshot_range_error() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "captured text range lies outside its snapshot backing",
    )
}

impl CapturedSnapshot {
    fn memory_bytes(&self) -> Option<&[u8]> {
        match &self.backing {
            SnapshotBacking::Memory(bytes) => Some(bytes),
            SnapshotBacking::Temp(_) => None,
        }
    }

    fn open_reader(&self, start: u64) -> io::Result<SnapshotReader<'_>> {
        match &self.backing {
            SnapshotBacking::Memory(bytes) => {
                let start = usize::try_from(start)
                    .unwrap_or(usize::MAX)
                    .min(bytes.len());
                Ok(SnapshotReader::Memory(Cursor::new(&bytes[start..])))
            }
            SnapshotBacking::Temp(snapshot) => snapshot.open_reader(start),
        }
    }

    fn shared_range(&self, start: u64) -> io::Result<SnapshotByteRange> {
        if start > self.len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "decoded text starts beyond the captured snapshot",
            ));
        }
        Ok(SnapshotByteRange {
            backing: self.backing.clone(),
            start,
            len: self.len - start,
        })
    }

    #[cfg(test)]
    fn temp_path(&self) -> Option<&Path> {
        match &self.backing {
            SnapshotBacking::Memory(_) => None,
            SnapshotBacking::Temp(snapshot) => Some(snapshot.file.path()),
        }
    }
}

/// Immutable bytes used by every encoding pass and by the regex search.
pub(crate) struct SealedSnapshot {
    path: PathRecord,
    _before: FileIdentity,
    _after: FileIdentity,
    pub(crate) paging_stamp: Option<PagingStamp>,
    captured: CapturedSnapshot,
}

impl SealedSnapshot {
    /// Returns the candidate whose original bytes produced this snapshot.
    pub(crate) fn path(&self) -> &PathRecord {
        &self.path
    }

    /// Returns the exact captured length, independent of traversal metadata.
    pub(crate) fn len(&self) -> u64 {
        self.captured.len
    }

    /// Borrows an in-memory backing without copying; temp-backed snapshots return `None`.
    pub(crate) fn memory_bytes(&self) -> Option<&[u8]> {
        self.captured.memory_bytes()
    }

    /// Borrows at most `maximum` leading bytes directly from an in-memory backing.
    pub(crate) fn memory_prefix(&self, maximum: usize) -> Option<&[u8]> {
        self.memory_bytes()
            .map(|bytes| &bytes[..bytes.len().min(maximum)])
    }

    /// Opens an independent reader over the same immutable backing at `start`.
    pub(crate) fn open_reader(&self, start: u64) -> io::Result<SnapshotReader<'_>> {
        self.captured.open_reader(start)
    }

    /// Shares the immutable suffix beginning at `start` without reopening the original path.
    pub(crate) fn shared_range(&self, start: u64) -> io::Result<SnapshotByteRange> {
        self.captured.shared_range(start)
    }
}

enum CaptureRead {
    Terminal(TerminalProof),
    Complete(CapturedSnapshot),
}

enum ClassifierMode {
    Explicit {
        encoding: String,
        decoder: StrictStreamingValidator,
        malformed: bool,
    },
    Bom {
        decoder: StrictStreamingValidator,
        encoding: &'static str,
        is_utf8: bool,
        malformed: bool,
    },
    Automatic {
        utf8: StrictStreamingValidator,
        utf8_malformed: bool,
        utf8_conflict: Utf8ConflictProbe,
        conflict_hex_offset: Option<usize>,
        fallback: Option<StrictStreamingValidator>,
        fallback_malformed: bool,
    },
}

/// Streaming-only state whose terminal decisions cannot be overturned by unread bytes.
struct CaptureClassifier {
    explicit_encoding: Option<String>,
    fallback_encoding: Option<String>,
    probe: Vec<u8>,
    mode: Option<ClassifierMode>,
}

impl CaptureClassifier {
    fn new(explicit_encoding: Option<&str>, fallback_encoding: Option<&str>) -> Self {
        Self {
            explicit_encoding: explicit_encoding.map(str::to_string),
            fallback_encoding: fallback_encoding.map(str::to_string),
            probe: Vec::with_capacity(PREFLIGHT_BYTES),
            mode: None,
        }
    }

    fn feed(&mut self, bytes: &[u8]) -> Result<Option<TerminalProof>, EncodingRejection> {
        let remaining_probe = PREFLIGHT_BYTES.saturating_sub(self.probe.len());
        self.probe
            .extend_from_slice(&bytes[..bytes.len().min(remaining_probe)]);

        if self.mode.is_none() {
            // Four bytes settle every BOM that can outrank the automatic NUL gate.
            if self.probe.len() < 4 {
                return Ok(None);
            }
            debug_assert!(bytes.len() <= PREFLIGHT_BYTES);
            self.initialize()?;
        } else {
            self.feed_initialized(bytes);
        }
        Ok(self.terminal_proof())
    }

    fn initialize(&mut self) -> Result<(), EncodingRejection> {
        debug_assert!(self.mode.is_none());
        if let Some(encoding) = self.explicit_encoding.clone() {
            let (mut decoder, bom_len) = explicit_streaming_validator(&encoding, &self.probe)?;
            let malformed = decoder.feed(&self.probe[bom_len..]);
            self.mode = Some(ClassifierMode::Explicit {
                encoding,
                decoder,
                malformed,
            });
            return Ok(());
        }

        if let Some(BomStreamingValidator {
            mut validator,
            bom_len,
            encoding,
            is_utf8,
        }) = bom_streaming_validator(&self.probe)
        {
            let malformed = validator.feed(&self.probe[bom_len..]);
            self.mode = Some(ClassifierMode::Bom {
                decoder: validator,
                encoding,
                is_utf8,
                malformed,
            });
            return Ok(());
        }

        let (mut utf8, bom_len) = explicit_streaming_validator("utf-8", &self.probe)
            .expect("the built-in UTF-8 label is valid");
        debug_assert_eq!(bom_len, 0);
        let utf8_malformed = utf8.feed(&self.probe);
        let mut utf8_conflict = Utf8ConflictProbe::new();
        let conflict_hex_offset = utf8_conflict.push(&self.probe);
        let (fallback, fallback_malformed) =
            if let Some(fallback_encoding) = self.fallback_encoding.as_deref() {
                let (mut fallback, bom_len) =
                    explicit_streaming_validator(fallback_encoding, &self.probe)?;
                debug_assert_eq!(bom_len, 0, "automatic mode has no BOM to strip");
                let malformed = fallback.feed(&self.probe);
                (Some(fallback), malformed)
            } else {
                (None, false)
            };
        self.mode = Some(ClassifierMode::Automatic {
            utf8,
            utf8_malformed,
            utf8_conflict,
            conflict_hex_offset,
            fallback,
            fallback_malformed,
        });
        Ok(())
    }

    fn feed_initialized(&mut self, bytes: &[u8]) {
        match self.mode.as_mut().expect("classifier mode is initialized") {
            ClassifierMode::Explicit {
                decoder, malformed, ..
            }
            | ClassifierMode::Bom {
                decoder, malformed, ..
            } => {
                *malformed |= decoder.feed(bytes);
            }
            ClassifierMode::Automatic {
                utf8,
                utf8_malformed,
                utf8_conflict,
                conflict_hex_offset,
                fallback,
                fallback_malformed,
            } => {
                *utf8_malformed |= utf8.feed(bytes);
                if conflict_hex_offset.is_none() {
                    *conflict_hex_offset = utf8_conflict.push(bytes);
                }
                if let Some(fallback) = fallback {
                    *fallback_malformed |= fallback.feed(bytes);
                }
            }
        }
    }

    fn finish_eof(&self) -> Option<TerminalProof> {
        // EOF-only incomplete sequences are deliberately non-terminal: an appended
        // suffix could complete them, so the sealed full-file validator decides them.
        self.terminal_proof()
    }

    fn terminal_proof(&self) -> Option<TerminalProof> {
        let mode = self.mode.as_ref()?;
        match mode {
            ClassifierMode::Explicit {
                encoding,
                malformed,
                ..
            } => malformed.then(|| TerminalProof::ExplicitDecoderMalformed {
                encoding: encoding.clone(),
            }),
            ClassifierMode::Bom {
                encoding,
                is_utf8,
                malformed,
                ..
            } => {
                if *is_utf8 && self.probe.contains(&0) {
                    return Some(TerminalProof::NulWithinFrozenProbe);
                }
                (*malformed && (!*is_utf8 || self.probe_is_settled()))
                    .then_some(TerminalProof::BomDecoderMalformed { encoding })
            }
            ClassifierMode::Automatic {
                utf8_malformed,
                conflict_hex_offset,
                fallback,
                fallback_malformed,
                ..
            } => {
                if self.probe.contains(&0) {
                    return Some(TerminalProof::NulWithinFrozenProbe);
                }
                if !self.probe_is_settled() {
                    return None;
                }
                if *utf8_malformed && detect_binary_type(&self.probe).is_some() {
                    return Some(TerminalProof::BinaryMagicAfterUtf8Failure);
                }
                let conflict_hex_offset = (*conflict_hex_offset)?;
                let fallback = match fallback {
                    None => FallbackTerminalState::Absent,
                    Some(_) if *fallback_malformed => FallbackTerminalState::PermanentlyMalformed,
                    Some(_) => return None,
                };
                Some(TerminalProof::AutomaticRejected {
                    conflict_hex_offset,
                    fallback,
                })
            }
        }
    }

    fn probe_is_settled(&self) -> bool {
        self.probe.len() == PREFLIGHT_BYTES
    }
}

enum SnapshotBuilder {
    Memory(Vec<u8>),
    Temp {
        file: tempfile::NamedTempFile,
        len: u64,
    },
}

impl SnapshotBuilder {
    fn new() -> Self {
        Self::Memory(Vec::with_capacity(PREFLIGHT_BYTES))
    }

    fn append(
        &mut self,
        bytes: &[u8],
        operation: Option<&dyn WorkCheckpoint>,
    ) -> Result<(), CaptureFailure> {
        let promote = matches!(
            self,
            Self::Memory(memory)
                if memory.len().saturating_add(bytes.len()) > MEMORY_SNAPSHOT_LIMIT
        );
        if promote {
            checkpoint(operation)?;
            #[cfg(test)]
            if let Some(operation) = operation {
                operation.stage(crate::operation::TestStage::SnapshotPromote);
            }
            checkpoint(operation)?;

            let memory = match std::mem::replace(self, Self::Memory(Vec::new())) {
                Self::Memory(memory) => memory,
                Self::Temp { .. } => unreachable!("promotion is only possible from memory"),
            };
            let mut file = match tempfile::NamedTempFile::new() {
                Ok(file) => file,
                Err(error) => {
                    return Err(prefer_stop(operation, CaptureFailure::Snapshot(error)));
                }
            };
            for chunk in memory.chunks(SNAPSHOT_CHUNK_BYTES) {
                write_snapshot_chunk(&mut file, chunk, operation)?;
            }
            let len = memory.len() as u64;
            *self = Self::Temp { file, len };
        }

        match self {
            Self::Memory(memory) => memory.extend_from_slice(bytes),
            Self::Temp { file, len } => {
                write_snapshot_chunk(file, bytes, operation)?;
                *len = len.saturating_add(bytes.len() as u64);
            }
        }
        Ok(())
    }

    fn finish(
        mut self,
        operation: Option<&dyn WorkCheckpoint>,
    ) -> Result<CapturedSnapshot, CaptureFailure> {
        match &mut self {
            Self::Memory(_) => {}
            Self::Temp { file, .. } => {
                checkpoint(operation)?;
                if let Err(error) = file.as_file_mut().flush() {
                    return Err(prefer_stop(operation, CaptureFailure::Snapshot(error)));
                }
                checkpoint(operation)?;
            }
        }
        Ok(match self {
            Self::Memory(memory) => CapturedSnapshot {
                len: memory.len() as u64,
                backing: SnapshotBacking::Memory(Arc::from(memory)),
            },
            Self::Temp { file, len } => CapturedSnapshot {
                len,
                backing: SnapshotBacking::Temp(Arc::new(TempSnapshot { file })),
            },
        })
    }
}

fn write_snapshot_chunk(
    file: &mut tempfile::NamedTempFile,
    bytes: &[u8],
    operation: Option<&dyn WorkCheckpoint>,
) -> Result<(), CaptureFailure> {
    debug_assert!(bytes.len() <= SNAPSHOT_CHUNK_BYTES);
    checkpoint(operation)?;
    if let Err(error) = file.as_file_mut().write_all(bytes) {
        return Err(prefer_stop(operation, CaptureFailure::Snapshot(error)));
    }
    checkpoint(operation)
}

fn capture_reader(
    reader: &mut impl Read,
    explicit_encoding: Option<&str>,
    fallback_encoding: Option<&str>,
    operation: Option<&dyn WorkCheckpoint>,
) -> Result<CaptureRead, CaptureFailure> {
    let mut builder = SnapshotBuilder::new();
    let mut classifier = CaptureClassifier::new(explicit_encoding, fallback_encoding);
    let mut chunk = [0_u8; SNAPSHOT_CHUNK_BYTES];
    let mut preflight_bytes = 0_usize;
    let mut reached_eof = false;

    while preflight_bytes < PREFLIGHT_BYTES {
        checkpoint(operation)?;
        #[cfg(test)]
        if let Some(operation) = operation {
            operation.stage(crate::operation::TestStage::CapturePreflightRead);
        }
        checkpoint(operation)?;
        let maximum = PREFLIGHT_BYTES - preflight_bytes;
        let count = match reader.read(&mut chunk[..maximum]) {
            Ok(count) => count,
            Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
        };
        checkpoint(operation)?;
        if count == 0 {
            reached_eof = true;
            break;
        }
        preflight_bytes += count;
        let proof = match classifier.feed(&chunk[..count]) {
            Ok(proof) => proof,
            Err(rejection) => {
                return Err(prefer_stop(
                    operation,
                    CaptureFailure::InvalidEncoding(rejection),
                ));
            }
        };
        checkpoint(operation)?;
        if let Some(proof) = proof {
            return Ok(CaptureRead::Terminal(proof));
        }
        builder.append(&chunk[..count], operation)?;
    }

    if !reached_eof {
        loop {
            checkpoint(operation)?;
            #[cfg(test)]
            if let Some(operation) = operation {
                operation.stage(crate::operation::TestStage::SnapshotChunk);
            }
            checkpoint(operation)?;
            let count = match reader.read(&mut chunk) {
                Ok(count) => count,
                Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
            };
            checkpoint(operation)?;
            if count == 0 {
                break;
            }
            let proof = match classifier.feed(&chunk[..count]) {
                Ok(proof) => proof,
                Err(rejection) => {
                    return Err(prefer_stop(
                        operation,
                        CaptureFailure::InvalidEncoding(rejection),
                    ));
                }
            };
            checkpoint(operation)?;
            if let Some(proof) = proof {
                return Ok(CaptureRead::Terminal(proof));
            }
            builder.append(&chunk[..count], operation)?;
        }
    }
    let proof = classifier.finish_eof();
    checkpoint(operation)?;
    if let Some(proof) = proof {
        return Ok(CaptureRead::Terminal(proof));
    }
    builder.finish(operation).map(CaptureRead::Complete)
}

fn checkpoint(operation: Option<&dyn WorkCheckpoint>) -> Result<(), CaptureFailure> {
    match operation.map(WorkCheckpoint::check_work) {
        Some(Err(WorkStop::RequestCancelled)) => Err(CaptureFailure::Cancelled),
        Some(Err(WorkStop::EpochRetired)) => Err(CaptureFailure::EpochRetired),
        Some(Ok(())) | None => Ok(()),
    }
}

fn prefer_stop(operation: Option<&dyn WorkCheckpoint>, failure: CaptureFailure) -> CaptureFailure {
    match checkpoint(operation) {
        Ok(()) => failure,
        Err(stop) => stop,
    }
}

#[cfg(not(windows))]
fn open_original(path: &Path) -> io::Result<File> {
    File::open(path)
}

#[cfg(windows)]
fn open_original(path: &Path) -> io::Result<File> {
    use std::os::windows::fs::OpenOptionsExt;
    use windows_sys::Win32::Storage::FileSystem::{
        FILE_SHARE_DELETE, FILE_SHARE_READ, FILE_SHARE_WRITE,
    };

    // Replacement must remain observable while the capture handle is live.
    std::fs::OpenOptions::new()
        .read(true)
        .share_mode(FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE)
        .open(path)
}

/// Opens the original candidate once, captures its bytes, and verifies stable identity.
pub(crate) fn capture_classify(
    candidate: &PathRecord,
    explicit_encoding: Option<&str>,
    fallback_encoding: Option<&str>,
    operation: Option<&dyn WorkCheckpoint>,
    paging_volume: Option<u64>,
) -> Result<CaptureDisposition, CaptureFailure> {
    checkpoint(operation)?;
    let mut file = match open_original(&candidate.native) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            checkpoint(operation)?;
            return Ok(CaptureDisposition::FileChanged);
        }
        Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
    };
    let (before, is_regular) = match identity_from_file(&file) {
        Ok(identity) => identity,
        Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
    };
    checkpoint(operation)?;
    if !is_regular || !before.matches_hint(candidate.traversal_fingerprint.as_ref()) {
        return Ok(CaptureDisposition::FileChanged);
    }

    let before_usn = paging_volume
        .filter(|volume| before.supports_paging(*volume))
        .and_then(|_| file_change_number(&file));
    let capture = capture_reader(&mut file, explicit_encoding, fallback_encoding, operation)?;
    checkpoint(operation)?;
    #[cfg(test)]
    if let Some(operation) = operation {
        operation.stage(crate::operation::TestStage::BeforeIdentityPostCheck);
    }
    checkpoint(operation)?;

    let (after, is_regular) = match identity_from_file(&file) {
        Ok(identity) => identity,
        Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
    };
    // A stamp is useful across requests only if the post-capture identity
    // check also confirms that no data-writing handle is still open.
    let guarded = before_usn.and_then(|_| paging_path_identity(&candidate.native).ok());
    let path_usn = guarded.as_ref().and_then(|(_, _, usn)| *usn);
    let path_identity = match guarded.map_or_else(
        || identity_from_path(&candidate.native),
        |(identity, regular, _)| Ok((identity, regular)),
    ) {
        Ok(identity) => identity,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            checkpoint(operation)?;
            return Ok(CaptureDisposition::FileChanged);
        }
        Err(error) => return Err(prefer_stop(operation, CaptureFailure::Io(error))),
    };
    checkpoint(operation)?;
    if !is_regular
        || !path_identity.1
        || !before.same_state(&after)
        || !after.same_state(&path_identity.0)
        || !after.matches_hint(candidate.traversal_fingerprint.as_ref())
    {
        return Ok(CaptureDisposition::FileChanged);
    }

    Ok(match capture {
        CaptureRead::Terminal(proof) => match proof.rejection() {
            Some(rejection) => CaptureDisposition::EncodingRejected { rejection, proof },
            None => CaptureDisposition::BinarySkipped(proof),
        },
        CaptureRead::Complete(captured) => {
            CaptureDisposition::Searchable(Box::new(SealedSnapshot {
                path: candidate.clone(),
                paging_stamp: path_usn
                    .filter(|usn| {
                        Some(*usn) == before_usn && before == after && after == path_identity.0
                    })
                    .map(|usn| PagingStamp {
                        identity: path_identity.0,
                        usn,
                    }),
                _before: before,
                _after: after,
                captured,
            }))
        }
    })
}

#[cfg(unix)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct FileIdentity {
    device: u64,
    inode: u64,
    len: u64,
    modified_seconds: i64,
    modified_nanoseconds: i64,
    changed_seconds: i64,
    changed_nanoseconds: i64,
}

#[cfg(unix)]
impl FileIdentity {
    fn from_metadata(metadata: &std::fs::Metadata) -> Self {
        use std::os::unix::fs::MetadataExt;
        Self {
            device: metadata.dev(),
            inode: metadata.ino(),
            len: metadata.len(),
            modified_seconds: metadata.mtime(),
            modified_nanoseconds: metadata.mtime_nsec(),
            changed_seconds: metadata.ctime(),
            changed_nanoseconds: metadata.ctime_nsec(),
        }
    }

    fn matches_hint(&self, hint: Option<&FileIdentityHint>) -> bool {
        hint.is_none_or(|hint| {
            self.device == hint.device
                && self.inode == hint.inode
                && self.len == hint.len
                && self.modified_seconds == hint.modified_seconds
                && self.modified_nanoseconds == hint.modified_nanoseconds
                && self.changed_seconds == hint.changed_seconds
                && self.changed_nanoseconds == hint.changed_nanoseconds
        })
    }

    fn same_state(&self, other: &Self) -> bool {
        self == other
    }

    fn supports_paging(&self, _volume: u64) -> bool {
        false
    }
}

#[cfg(unix)]
fn identity_from_file(file: &File) -> io::Result<(FileIdentity, bool)> {
    let metadata = file.metadata()?;
    Ok((FileIdentity::from_metadata(&metadata), metadata.is_file()))
}

#[cfg(unix)]
fn identity_from_path(path: &Path) -> io::Result<(FileIdentity, bool)> {
    let metadata = std::fs::metadata(path)?;
    Ok((FileIdentity::from_metadata(&metadata), metadata.is_file()))
}

#[cfg(windows)]
#[derive(Clone, Debug, Eq, PartialEq)]
enum WindowsFileId {
    Extended {
        volume_serial: u64,
        identifier: [u8; 16],
    },
    Legacy {
        volume_serial: u32,
        file_index: u64,
    },
}

#[cfg(windows)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct FileIdentity {
    file_id: WindowsFileId,
    len: u64,
    creation_time: u64,
    last_write_time: u64,
    change_time: Option<i64>,
    attributes: u32,
}

#[cfg(windows)]
impl FileIdentity {
    fn from_file(file: &File) -> io::Result<Self> {
        use std::mem::size_of;
        use std::os::windows::io::AsRawHandle;
        use windows_sys::Win32::Foundation::{ERROR_INVALID_PARAMETER, ERROR_NOT_SUPPORTED};
        use windows_sys::Win32::Storage::FileSystem::{
            BY_HANDLE_FILE_INFORMATION, FILE_BASIC_INFO, FILE_ID_INFO, FileBasicInfo, FileIdInfo,
            GetFileInformationByHandle, GetFileInformationByHandleEx,
        };

        let handle = file.as_raw_handle();
        let mut info = BY_HANDLE_FILE_INFORMATION::default();
        let ok = unsafe { GetFileInformationByHandle(handle, &mut info) };
        if ok == 0 {
            return Err(io::Error::last_os_error());
        }
        let mut extended_id = FILE_ID_INFO::default();
        let extended_id_ok = unsafe {
            GetFileInformationByHandleEx(
                handle,
                FileIdInfo,
                (&mut extended_id as *mut FILE_ID_INFO).cast(),
                size_of::<FILE_ID_INFO>() as u32,
            )
        };
        let file_id = if extended_id_ok != 0 {
            WindowsFileId::Extended {
                volume_serial: extended_id.VolumeSerialNumber,
                identifier: extended_id.FileId.Identifier,
            }
        } else {
            let error = io::Error::last_os_error();
            match error.raw_os_error() {
                Some(code)
                    if code == ERROR_NOT_SUPPORTED as i32
                        || code == ERROR_INVALID_PARAMETER as i32 =>
                {
                    WindowsFileId::Legacy {
                        volume_serial: info.dwVolumeSerialNumber,
                        file_index: (u64::from(info.nFileIndexHigh) << 32)
                            | u64::from(info.nFileIndexLow),
                    }
                }
                _ => return Err(error),
            }
        };
        let mut basic = FILE_BASIC_INFO::default();
        let basic_ok = unsafe {
            GetFileInformationByHandleEx(
                handle,
                FileBasicInfo,
                (&mut basic as *mut FILE_BASIC_INFO).cast(),
                size_of::<FILE_BASIC_INFO>() as u32,
            )
        };
        Ok(Self {
            file_id,
            len: (u64::from(info.nFileSizeHigh) << 32) | u64::from(info.nFileSizeLow),
            creation_time: filetime_u64(info.ftCreationTime),
            last_write_time: filetime_u64(info.ftLastWriteTime),
            change_time: (basic_ok != 0).then_some(basic.ChangeTime),
            attributes: info.dwFileAttributes,
        })
    }

    fn matches_hint(&self, hint: Option<&FileIdentityHint>) -> bool {
        // Stable Windows file IDs are handle-only; traversal metadata can compare
        // only these fields, while the before/after/path handle checks compare IDs.
        hint.is_none_or(|hint| {
            self.len == hint.len
                && self.creation_time == hint.creation_time
                && self.last_write_time == hint.last_write_time
                && self.attributes == hint.attributes
        })
    }

    fn same_state(&self, other: &Self) -> bool {
        self.file_id == other.file_id
            && self.len == other.len
            && self.creation_time == other.creation_time
            && self.last_write_time == other.last_write_time
            && self.attributes == other.attributes
            && match (self.change_time, other.change_time) {
                (Some(left), Some(right)) => left == right,
                _ => true,
            }
    }

    fn supports_paging(&self, volume: u64) -> bool {
        matches!(self.file_id, WindowsFileId::Extended { volume_serial, .. } if volume_serial == volume)
            && self.change_time.is_some_and(|time| time > 0)
    }
}

/// A previously checked file identity, reusable only on the search root's NTFS volume.
#[derive(Clone, Debug)]
pub(crate) struct PagingStamp {
    identity: FileIdentity,
    usn: i64,
}

impl PagingStamp {
    pub(crate) fn matches(&self, candidate: &PathRecord) -> bool {
        paging_path_identity(&candidate.native).is_ok_and(|(current, regular, usn)| {
            regular
                && self.identity == current
                && Some(self.usn) == usn
                && current.matches_hint(candidate.traversal_fingerprint.as_ref())
        })
    }
}

#[cfg(windows)]
fn paging_path_identity(path: &Path) -> io::Result<(FileIdentity, bool, Option<i64>)> {
    use std::os::windows::fs::OpenOptionsExt;
    use windows_sys::Win32::Storage::FileSystem::{FILE_SHARE_DELETE, FILE_SHARE_READ};

    // A writer can keep Windows timestamps pending until it closes. Treat a
    // sharing conflict as a cache miss. Delete sharing keeps replacements observable.
    let file = std::fs::OpenOptions::new()
        .read(true)
        .share_mode(FILE_SHARE_READ | FILE_SHARE_DELETE)
        .open(path)?;
    let (identity, regular) = identity_from_file(&file)?;
    Ok((identity, regular, file_change_number(&file)))
}

#[cfg(not(windows))]
fn paging_path_identity(path: &Path) -> io::Result<(FileIdentity, bool, Option<i64>)> {
    identity_from_path(path).map(|(identity, regular)| (identity, regular, None))
}

#[cfg(windows)]
fn file_change_number(file: &File) -> Option<i64> {
    use std::mem::{offset_of, size_of};
    use std::os::windows::io::AsRawHandle;
    use windows_sys::Win32::System::IO::DeviceIoControl;
    use windows_sys::Win32::System::Ioctl::{
        FSCTL_READ_FILE_USN_DATA, READ_FILE_USN_DATA, USN_RECORD_V2, USN_RECORD_V3,
    };

    let input = READ_FILE_USN_DATA {
        MinMajorVersion: 2,
        MaxMajorVersion: 3,
    };
    let mut record = [0_u8; 1024];
    let mut received = 0_u32;
    let ok = unsafe {
        DeviceIoControl(
            file.as_raw_handle(),
            FSCTL_READ_FILE_USN_DATA,
            (&raw const input).cast(),
            size_of::<READ_FILE_USN_DATA>() as u32,
            record.as_mut_ptr().cast(),
            record.len() as u32,
            &mut received,
            std::ptr::null_mut(),
        )
    };
    if ok == 0 {
        return None;
    }
    let record = record.get(..received as usize)?;
    let version = u16::from_le_bytes(record.get(4..6)?.try_into().ok()?);
    let start = match version {
        2 => offset_of!(USN_RECORD_V2, Usn),
        3 => offset_of!(USN_RECORD_V3, Usn),
        _ => return None,
    };
    let usn = i64::from_le_bytes(record.get(start..start + 8)?.try_into().ok()?);
    (usn > 0).then_some(usn)
}

#[cfg(not(windows))]
fn file_change_number(_file: &File) -> Option<i64> {
    None
}

pub(crate) struct PagingVolume {
    pub(crate) serial: u64,
    pub(crate) journal_id: u64,
    directory: File,
}

impl PagingVolume {
    pub(crate) fn journal_unchanged(&self) -> bool {
        query_journal_id(&self.directory) == Some(self.journal_id)
    }
}

#[cfg(windows)]
fn query_journal_id(directory: &File) -> Option<u64> {
    use std::mem::size_of;
    use std::os::windows::io::AsRawHandle;
    use windows_sys::Win32::System::IO::DeviceIoControl;
    use windows_sys::Win32::System::Ioctl::{FSCTL_QUERY_USN_JOURNAL, USN_JOURNAL_DATA_V2};

    let mut info = USN_JOURNAL_DATA_V2::default();
    let mut received = 0_u32;
    let ok = unsafe {
        DeviceIoControl(
            directory.as_raw_handle(),
            FSCTL_QUERY_USN_JOURNAL,
            std::ptr::null(),
            0,
            (&raw mut info).cast(),
            size_of::<USN_JOURNAL_DATA_V2>() as u32,
            &mut received,
            std::ptr::null_mut(),
        )
    };
    (ok != 0 && received >= size_of::<u64>() as u32 && info.UsnJournalID != 0)
        .then_some(info.UsnJournalID)
}

#[cfg(not(windows))]
fn query_journal_id(_directory: &File) -> Option<u64> {
    None
}

#[cfg(windows)]
pub(crate) fn paging_volume(path: &Path) -> Option<PagingVolume> {
    use std::os::windows::{fs::OpenOptionsExt, io::AsRawHandle};
    use std::path::{Component, Prefix};
    use windows_sys::Win32::Storage::FileSystem::{
        FILE_FLAG_BACKUP_SEMANTICS, FILE_READ_ATTRIBUTES, GetDriveTypeW,
        GetVolumeInformationByHandleW,
    };

    let Some(Component::Prefix(prefix)) = path.components().next() else {
        return None;
    };
    let (Prefix::Disk(letter) | Prefix::VerbatimDisk(letter)) = prefix.kind() else {
        return None;
    };
    let drive = [u16::from(letter), b':' as u16, b'\\' as u16, 0];
    const DRIVE_FIXED: u32 = 3;
    if unsafe { GetDriveTypeW(drive.as_ptr()) } != DRIVE_FIXED {
        return None;
    }
    let directory = std::fs::OpenOptions::new()
        .access_mode(FILE_READ_ATTRIBUTES)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS)
        .open(path)
        .ok()?;
    let mut name = [0_u16; 16];
    let ok = unsafe {
        GetVolumeInformationByHandleW(
            directory.as_raw_handle(),
            std::ptr::null_mut(),
            0,
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            name.as_mut_ptr(),
            name.len() as u32,
        )
    };
    if ok == 0 || name[..5] != [b'N' as u16, b'T' as u16, b'F' as u16, b'S' as u16, 0] {
        return None;
    }
    let WindowsFileId::Extended {
        volume_serial: serial,
        ..
    } = FileIdentity::from_file(&directory).ok()?.file_id
    else {
        return None;
    };
    let journal_id = query_journal_id(&directory)?;
    Some(PagingVolume {
        serial,
        journal_id,
        directory,
    })
}

#[cfg(not(windows))]
pub(crate) fn paging_volume(_path: &Path) -> Option<PagingVolume> {
    None
}

#[cfg(windows)]
fn filetime_u64(value: windows_sys::Win32::Foundation::FILETIME) -> u64 {
    (u64::from(value.dwHighDateTime) << 32) | u64::from(value.dwLowDateTime)
}

#[cfg(windows)]
fn identity_from_file(file: &File) -> io::Result<(FileIdentity, bool)> {
    use windows_sys::Win32::Storage::FileSystem::{
        FILE_ATTRIBUTE_DIRECTORY, FILE_ATTRIBUTE_REPARSE_POINT,
    };

    let identity = FileIdentity::from_file(file)?;
    // Reparse points need the tag-aware classification from std. Ordinary
    // handles already supplied the directory bit in the same identity read.
    let regular = if identity.attributes & FILE_ATTRIBUTE_REPARSE_POINT != 0 {
        file.metadata()?.is_file()
    } else {
        identity.attributes & FILE_ATTRIBUTE_DIRECTORY == 0
    };
    Ok((identity, regular))
}

#[cfg(windows)]
fn identity_from_path(path: &Path) -> io::Result<(FileIdentity, bool)> {
    use std::os::windows::fs::OpenOptionsExt;
    use windows_sys::Win32::Storage::FileSystem::{
        FILE_READ_ATTRIBUTES, FILE_SHARE_DELETE, FILE_SHARE_READ, FILE_SHARE_WRITE,
    };

    // Windows path metadata omits the stable file index, so this attributes-only
    // handle is required to prove that the path still names the captured file.
    let file = std::fs::OpenOptions::new()
        .access_mode(FILE_READ_ATTRIBUTES)
        .share_mode(FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE)
        .open(path)?;
    identity_from_file(&file)
}

#[cfg(test)]
mod tests {
    use super::{
        CaptureDisposition, CaptureFailure, CaptureRead, FallbackTerminalState,
        MEMORY_SNAPSHOT_LIMIT, PREFLIGHT_BYTES, SNAPSHOT_CHUNK_BYTES, TerminalProof,
        capture_classify, capture_reader,
    };
    use crate::encoding::{
        ByteSource, EncodingDecision, EncodingRejection, validate_source_encoding,
    };
    use crate::operation::{RequestWorkGuard, TestStage};
    use crate::path_codec::PathRecord;

    use filetime::{FileTime, set_file_mtime};
    use rmcp::model::RequestId;
    use std::io::{self, Read, Write};
    use std::sync::Arc;

    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use tokio_util::sync::CancellationToken;

    struct ChunkedReader {
        bytes: Vec<u8>,
        position: usize,
        maximum: usize,
        fail_at: Option<usize>,
        reads: usize,
        requested: Vec<usize>,
        position_counter: Option<Arc<AtomicUsize>>,
        read_limits: Option<Vec<usize>>,
    }

    impl ChunkedReader {
        fn new(bytes: Vec<u8>, maximum: usize) -> Self {
            Self {
                bytes,
                position: 0,
                maximum,
                fail_at: None,
                reads: 0,
                requested: Vec::new(),
                position_counter: None,
                read_limits: None,
            }
        }

        fn with_position_counter(mut self, position: Arc<AtomicUsize>) -> Self {
            self.position_counter = Some(position);
            self
        }

        fn with_read_limits(mut self, read_limits: Vec<usize>) -> Self {
            assert!(!read_limits.is_empty());
            assert!(read_limits.iter().all(|limit| *limit > 0));
            self.read_limits = Some(read_limits);
            self
        }
    }

    impl Read for ChunkedReader {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            self.reads += 1;
            self.requested.push(output.len());
            if self.fail_at.is_some_and(|offset| self.position >= offset) {
                return Err(io::Error::other("injected read failure"));
            }
            if self.position >= self.bytes.len() {
                return Ok(0);
            }
            let read_limit = self.read_limits.as_ref().map_or(self.maximum, |limits| {
                limits[(self.reads - 1) % limits.len()]
            });
            let count = output
                .len()
                .min(self.maximum)
                .min(read_limit)
                .min(self.bytes.len() - self.position);
            output[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
            self.position += count;
            if let Some(position) = &self.position_counter {
                position.store(self.position, Ordering::Release);
            }
            Ok(count)
        }
    }

    #[derive(Debug, Eq, PartialEq)]
    enum ReferenceDisposition {
        Text { used_fallback: bool },
        Binary,
        Rejected(EncodingRejection),
    }

    fn reference_disposition(
        bytes: &[u8],
        explicit: Option<&str>,
        fallback: Option<&str>,
    ) -> ReferenceDisposition {
        let source = ByteSource::Bytes(bytes);
        match validate_source_encoding(source, explicit).unwrap() {
            EncodingDecision::Text(_) => ReferenceDisposition::Text {
                used_fallback: false,
            },
            EncodingDecision::Binary => ReferenceDisposition::Binary,
            EncodingDecision::Rejected(rejection) => {
                if explicit.is_none()
                    && !matches!(rejection, EncodingRejection::BomMismatch { .. })
                    && let Some(fallback) = fallback
                    && matches!(
                        validate_source_encoding(source, Some(fallback)).unwrap(),
                        EncodingDecision::Text(_)
                    )
                {
                    ReferenceDisposition::Text {
                        used_fallback: true,
                    }
                } else {
                    ReferenceDisposition::Rejected(rejection)
                }
            }
        }
    }

    fn proof_disposition(proof: &TerminalProof) -> ReferenceDisposition {
        proof
            .rejection()
            .map_or(ReferenceDisposition::Binary, ReferenceDisposition::Rejected)
    }

    fn mixed_prefix() -> Vec<u8> {
        let mut bytes = "界".repeat(11).into_bytes();
        debug_assert_eq!(bytes.len(), 33);
        bytes.push(0xFF);
        bytes.resize(PREFLIGHT_BYTES, b'a');
        bytes
    }

    #[test]
    fn every_production_terminal_proof_is_suffix_invariant_against_the_reference() {
        let cases = [
            (
                "nul",
                vec![b'a', 0, b'b', b'c'],
                None,
                None,
                TerminalProof::NulWithinFrozenProbe,
            ),
            (
                "binary magic",
                {
                    let mut bytes = b"\x1F\x8B".to_vec();
                    bytes.resize(PREFLIGHT_BYTES, b'a');
                    bytes
                },
                None,
                None,
                TerminalProof::BinaryMagicAfterUtf8Failure,
            ),
            (
                "explicit malformed",
                vec![b'a', b'b', b'c', 0xFF],
                Some("utf-8"),
                None,
                TerminalProof::ExplicitDecoderMalformed {
                    encoding: "utf-8".to_string(),
                },
            ),
            (
                "explicit matching BOM malformed",
                b"\xFF\xFE\x00\x00\x00\x00\x11\x00".to_vec(),
                Some("utf-32le"),
                None,
                TerminalProof::ExplicitDecoderMalformed {
                    encoding: "utf-32le".to_string(),
                },
            ),
            (
                "BOM malformed",
                b"\xFF\xFE\x00\x00\x00\x00\x11\x00".to_vec(),
                None,
                None,
                TerminalProof::BomDecoderMalformed {
                    encoding: "UTF-32LE",
                },
            ),
            (
                "UTF-8 BOM malformed after NUL gate",
                {
                    let mut bytes = b"\xEF\xBB\xBF\xFF".to_vec();
                    bytes.resize(PREFLIGHT_BYTES, b'a');
                    bytes
                },
                None,
                None,
                TerminalProof::BomDecoderMalformed { encoding: "UTF-8" },
            ),
            (
                "automatic mixed without fallback",
                mixed_prefix(),
                None,
                None,
                TerminalProof::AutomaticRejected {
                    conflict_hex_offset: 3,
                    fallback: FallbackTerminalState::Absent,
                },
            ),
            (
                "automatic mixed with permanently malformed fallback",
                mixed_prefix(),
                None,
                Some("utf-8"),
                TerminalProof::AutomaticRejected {
                    conflict_hex_offset: 3,
                    fallback: FallbackTerminalState::PermanentlyMalformed,
                },
            ),
        ];
        let mut suffixes = vec![
            Vec::new(),
            b"plain utf-8".to_vec(),
            vec![0; 257],
            vec![0x80; 257],
            (0..4096).map(|index| (index * 73) as u8).collect(),
        ];
        suffixes.extend((0_u16..=u8::MAX as u16).map(|byte| vec![byte as u8]));
        for (name, prefix, explicit, fallback, expected_proof) in cases {
            for suffix in &suffixes {
                let mut bytes = prefix.clone();
                bytes.extend_from_slice(suffix);
                let expected = reference_disposition(&bytes, explicit, fallback);
                for maximum in [1, 2, 3, 7, 127, PREFLIGHT_BYTES] {
                    let mut reader = ChunkedReader::new(bytes.clone(), maximum);
                    reader.fail_at = Some(prefix.len());
                    let CaptureRead::Terminal(proof) =
                        capture_reader(&mut reader, explicit, fallback, None).unwrap()
                    else {
                        panic!("{name}: expected terminal proof at chunk size {maximum}");
                    };
                    assert_eq!(proof, expected_proof, "{name}, chunk size {maximum}");
                    assert_eq!(
                        proof_disposition(&proof),
                        expected,
                        "{name}, chunk size {maximum}, suffix length {}",
                        suffix.len()
                    );
                    assert!(
                        reader.position
                            <= prefix
                                .len()
                                .saturating_add(maximum.saturating_sub(1))
                                .min(bytes.len()),
                        "{name}, chunk size {maximum}: reader crossed a second read after proof"
                    );
                }
            }

            let suffix = (0..4096)
                .map(|index| (index * 151 + 17) as u8)
                .collect::<Vec<_>>();
            let mut bytes = prefix.clone();
            bytes.extend_from_slice(&suffix);
            let expected = reference_disposition(&bytes, explicit, fallback);
            let mut random_state = 0xA5A5_1F3D_u32;
            let read_limits = (0..64)
                .map(|_| {
                    random_state ^= random_state << 13;
                    random_state ^= random_state >> 17;
                    random_state ^= random_state << 5;
                    (random_state as usize % 1024) + 1
                })
                .collect();
            let mut reader = ChunkedReader::new(bytes, usize::MAX).with_read_limits(read_limits);
            reader.fail_at = Some(prefix.len());
            let CaptureRead::Terminal(proof) =
                capture_reader(&mut reader, explicit, fallback, None).unwrap()
            else {
                panic!("{name}: expected terminal proof at randomized chunk boundaries");
            };
            assert_eq!(proof, expected_proof, "{name}, randomized chunks");
            assert_eq!(
                proof_disposition(&proof),
                expected,
                "{name}, randomized chunks"
            );
        }
    }

    #[test]
    fn large_capture_promotes_once_reads_repeatably_and_unlinks_on_drop() {
        let bytes = vec![b'x'; MEMORY_SNAPSHOT_LIMIT + 1];
        let mut reader = ChunkedReader::new(bytes.clone(), 17 * 1024);
        let promotions = Arc::new(AtomicUsize::new(0));
        let promotions_for_hook = Arc::clone(&promotions);
        let hook = Arc::new(move |stage| {
            if stage == TestStage::SnapshotPromote {
                promotions_for_hook.fetch_add(1, Ordering::AcqRel);
            }
        });
        let (mut guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(10), CancellationToken::new(), hook);
        let CaptureRead::Complete(snapshot) =
            capture_reader(&mut reader, None, None, Some(&operation)).unwrap()
        else {
            panic!("expected complete snapshot");
        };
        guard.disarm();
        assert_eq!(promotions.load(Ordering::Acquire), 1);
        assert_eq!(reader.requested.first(), Some(&PREFLIGHT_BYTES));
        assert!(
            reader
                .requested
                .iter()
                .all(|requested| *requested <= SNAPSHOT_CHUNK_BYTES)
        );
        let temp_path = snapshot.temp_path().unwrap().to_path_buf();
        assert!(temp_path.exists());
        assert_eq!(snapshot.len, bytes.len() as u64);
        for _ in 0..2 {
            let mut reopened = snapshot.open_reader(0).unwrap();
            let mut actual = Vec::new();
            reopened.read_to_end(&mut actual).unwrap();
            assert_eq!(actual, bytes);
        }
        drop(snapshot);
        assert!(!temp_path.exists());
    }

    #[test]
    fn cancellation_at_capture_stages_stops_within_the_declared_read_boundary() {
        let preflight_token = CancellationToken::new();
        let token_for_hook = preflight_token.clone();
        let hook = Arc::new(move |stage| {
            if stage == TestStage::CapturePreflightRead {
                token_for_hook.cancel();
            }
        });
        let (_guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(11), preflight_token, hook);
        let mut reader = ChunkedReader::new(vec![b'a'; PREFLIGHT_BYTES + 1], usize::MAX);
        assert!(matches!(
            capture_reader(&mut reader, None, None, Some(&operation)),
            Err(CaptureFailure::Cancelled)
        ));
        assert_eq!(reader.position, 0);

        let stream_token = CancellationToken::new();
        let token_for_hook = stream_token.clone();
        let hook = Arc::new(move |stage| {
            if stage == TestStage::SnapshotChunk {
                token_for_hook.cancel();
            }
        });
        let (_guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(12), stream_token, hook);
        let mut reader = ChunkedReader::new(vec![b'a'; PREFLIGHT_BYTES + 1], usize::MAX);
        assert!(matches!(
            capture_reader(&mut reader, None, None, Some(&operation)),
            Err(CaptureFailure::Cancelled)
        ));
        assert_eq!(reader.position, PREFLIGHT_BYTES);

        let promote_token = CancellationToken::new();
        let token_for_hook = promote_token.clone();
        let promotions = Arc::new(AtomicUsize::new(0));
        let promotions_for_hook = Arc::clone(&promotions);
        let hook = Arc::new(move |stage| {
            if stage == TestStage::SnapshotPromote {
                promotions_for_hook.fetch_add(1, Ordering::AcqRel);
                token_for_hook.cancel();
            }
        });
        let (_guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(13), promote_token, hook);
        let position = Arc::new(AtomicUsize::new(0));
        let mut reader = ChunkedReader::new(vec![b'a'; MEMORY_SNAPSHOT_LIMIT + 1], usize::MAX)
            .with_position_counter(Arc::clone(&position));
        assert!(matches!(
            capture_reader(&mut reader, None, None, Some(&operation)),
            Err(CaptureFailure::Cancelled)
        ));
        assert_eq!(promotions.load(Ordering::Acquire), 1);
        assert!(position.load(Ordering::Acquire) <= MEMORY_SNAPSHOT_LIMIT + SNAPSHOT_CHUNK_BYTES);
    }

    #[test]
    fn sealed_temp_snapshot_survives_original_removal_for_all_later_passes() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("large-searchable.txt");
        let mut bytes = vec![b'a'; MEMORY_SNAPSHOT_LIMIT + 1];
        bytes.extend_from_slice(b"\nneedle\n");
        std::fs::write(&path, &bytes).unwrap();
        let metadata = std::fs::metadata(&path).unwrap();
        let candidate = PathRecord::from_metadata(&path, temp.path(), &metadata, true).unwrap();
        let CaptureDisposition::Searchable(snapshot) =
            capture_classify(&candidate, None, None, None, None).unwrap()
        else {
            panic!("expected searchable snapshot");
        };
        let temp_path = snapshot.captured.temp_path().unwrap().to_path_buf();
        std::fs::remove_file(&path).unwrap();

        let source = ByteSource::Snapshot(&snapshot);
        let EncodingDecision::Text(validated) = validate_source_encoding(source, None).unwrap()
        else {
            panic!("expected trusted UTF-8 snapshot");
        };
        let mut reader = validated.open_source_reader(source).unwrap();
        let mut actual = Vec::new();
        reader.read_to_end(&mut actual).unwrap();
        assert_eq!(actual, bytes);
        assert!(temp_path.exists());
        drop(reader);
        let shared = snapshot.shared_range(0).unwrap();
        drop(snapshot);
        assert!(temp_path.exists());
        let mut shared_reader = shared.open_reader().unwrap();
        let mut shared_bytes = Vec::new();
        shared_reader.read_to_end(&mut shared_bytes).unwrap();
        assert_eq!(shared_bytes, bytes);
        drop(shared_reader);
        assert_eq!(
            shared
                .read_range((bytes.len() - 7) as u64..bytes.len() as u64)
                .unwrap(),
            b"needle\n"
        );
        drop(shared);
        assert!(!temp_path.exists());
    }

    #[test]
    fn traversal_mismatch_and_post_capture_mutation_are_file_changed() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("changing.txt");
        std::fs::write(&path, b"before").unwrap();
        let metadata = std::fs::metadata(&path).unwrap();
        let candidate = PathRecord::from_metadata(&path, temp.path(), &metadata, true).unwrap();
        std::fs::write(&path, b"different length").unwrap();
        assert!(matches!(
            capture_classify(&candidate, None, None, None, None).unwrap(),
            CaptureDisposition::FileChanged
        ));

        std::fs::write(&path, b"same-one").unwrap();
        set_file_mtime(&path, FileTime::from_unix_time(1_700_000_000, 0)).unwrap();
        let metadata = std::fs::metadata(&path).unwrap();
        let candidate = PathRecord::from_metadata(&path, temp.path(), &metadata, true).unwrap();
        std::fs::write(&path, b"same-two").unwrap();
        set_file_mtime(&path, FileTime::from_unix_time(1_700_000_010, 0)).unwrap();
        assert!(matches!(
            capture_classify(&candidate, None, None, None, None).unwrap(),
            CaptureDisposition::FileChanged
        ));

        std::fs::write(&path, b"stable bytes").unwrap();
        let metadata = std::fs::metadata(&path).unwrap();
        let candidate = PathRecord::from_metadata(&path, temp.path(), &metadata, true).unwrap();
        let changed = Arc::new(AtomicBool::new(false));
        let changed_for_hook = Arc::clone(&changed);
        let path_for_hook = path.clone();
        let hook = Arc::new(move |stage| {
            if stage == TestStage::BeforeIdentityPostCheck
                && !changed_for_hook.swap(true, Ordering::AcqRel)
            {
                let mut file = std::fs::OpenOptions::new()
                    .write(true)
                    .truncate(true)
                    .open(&path_for_hook)
                    .unwrap();
                file.write_all(b"mutated to another length").unwrap();
                file.flush().unwrap();
            }
        });
        let (mut guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(1), CancellationToken::new(), hook);
        assert!(matches!(
            capture_classify(&candidate, None, None, Some(&operation), None).unwrap(),
            CaptureDisposition::FileChanged
        ));
        guard.disarm();
        assert!(changed.load(Ordering::Acquire));

        std::fs::write(&path, b"stable replacement bytes").unwrap();
        let metadata = std::fs::metadata(&path).unwrap();
        let candidate = PathRecord::from_metadata(&path, temp.path(), &metadata, true).unwrap();
        let replaced = Arc::new(AtomicBool::new(false));
        let replaced_for_hook = Arc::clone(&replaced);
        let path_for_hook = path.clone();
        let old_path = temp.path().join("captured-old.txt");
        let hook = Arc::new(move |stage| {
            if stage == TestStage::BeforeIdentityPostCheck
                && !replaced_for_hook.swap(true, Ordering::AcqRel)
            {
                std::fs::rename(&path_for_hook, &old_path).unwrap();
                std::fs::write(&path_for_hook, b"stable replacement bytes").unwrap();
            }
        });
        let (mut guard, operation) =
            RequestWorkGuard::new_with_hook(RequestId::Number(2), CancellationToken::new(), hook);
        assert!(matches!(
            capture_classify(&candidate, None, None, Some(&operation), None).unwrap(),
            CaptureDisposition::FileChanged
        ));
        guard.disarm();
        assert!(replaced.load(Ordering::Acquire));
    }
}
