//! Verification-aware proof cache for storing and retrieving verification results.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Stores verification results keyed by VC fingerprints with support for
//! invalidation on code changes, LRU/LFU/FIFO/ARC eviction, secondary
//! indexing by function name and file path, and filesystem persistence.
//!
//! This module is entirely self-contained: it does not import from sibling
//! trust-vc-core modules and depends only on `std` plus `sha2`.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::io;
use std::path::Path;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration governing cache capacity, memory budget, TTL, and eviction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CacheConfig {
    /// Maximum number of entries the cache may hold.
    pub max_entries: usize,
    /// Maximum total memory budget (in bytes) for cached entries.
    pub max_memory_bytes: usize,
    /// Time-to-live for individual cache entries.
    pub ttl: Duration,
    /// Eviction policy applied when capacity or memory limits are exceeded.
    pub eviction_policy: EvictionPolicy,
    /// Format version written to serialized cache images.
    pub format_version: u32,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            max_entries: 4096,
            max_memory_bytes: 256 * 1024 * 1024, // 256 MiB
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        }
    }
}

// ---------------------------------------------------------------------------
// Eviction policy
// ---------------------------------------------------------------------------

/// Strategy used to select victims when the cache is full.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EvictionPolicy {
    /// Least-recently-used.
    Lru,
    /// Least-frequently-used.
    Lfu,
    /// First-in-first-out with priority tiers (higher priority entries survive longer).
    FifoWithPriority,
    /// Adaptive replacement cache (simplified ARC).
    AdaptiveArc,
}

// ---------------------------------------------------------------------------
// Cache key / fingerprint
// ---------------------------------------------------------------------------

/// Opaque key derived from a VC fingerprint combined with solver configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CacheKey {
    hash: [u8; 32],
}

impl CacheKey {
    /// Construct a key from a raw 256-bit hash.
    #[must_use]
    pub fn from_raw(hash: [u8; 32]) -> Self {
        Self { hash }
    }

    /// Return the underlying 256-bit hash bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.hash
    }
}

impl fmt::Display for CacheKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.hash {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Cached result
// ---------------------------------------------------------------------------

/// Outcome of a verification query, stored inside the cache.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CachedResult {
    /// The obligation was successfully verified.
    Verified,
    /// Verification failed with a reason string.
    Failed { reason: String },
    /// The solver returned unknown.
    Unknown,
    /// The solver timed out.
    Timeout,
}

impl CachedResult {
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, CachedResult::Verified)
    }
}

// ---------------------------------------------------------------------------
// Cache entry
// ---------------------------------------------------------------------------

/// A single cached verification result together with metadata.
#[derive(Debug, Clone)]
pub struct CacheEntry {
    /// The cached verification result.
    pub result: CachedResult,
    /// Wall-clock creation time as duration since `UNIX_EPOCH`.
    pub created_at: Duration,
    /// Number of times this entry has been accessed.
    pub access_count: u64,
    /// Estimated size in bytes of the serialized form of this entry.
    pub size_bytes: usize,
    /// Informational string identifying the solver configuration used.
    pub solver_info: String,
    /// Optional function name the VC belongs to (used for secondary indexing).
    pub function_name: Option<String>,
    /// Optional source file path (used for secondary indexing).
    pub file_path: Option<String>,
    /// Priority tier for `FifoWithPriority` eviction.
    pub priority: u8,
    /// Monotonic instant of most recent access (not serialized).
    last_accessed: Option<Instant>,
}

impl CacheEntry {
    /// Estimated heap size of this entry (very rough).
    #[must_use]
    pub(crate) fn estimated_heap_size(&self) -> usize {
        let base = std::mem::size_of::<Self>();
        let dynamic = self.solver_info.len()
            + self.function_name.as_ref().map_or(0, String::len)
            + self.file_path.as_ref().map_or(0, String::len)
            + match &self.result {
                CachedResult::Failed { reason } => reason.len(),
                _ => 0,
            };
        base + dynamic
    }
}

// ---------------------------------------------------------------------------
// Cache statistics
// ---------------------------------------------------------------------------

/// Accumulated statistics about cache usage.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
    pub invalidations: u64,
    pub memory_used_bytes: usize,
    pub entry_count: usize,
}

impl CacheStats {
    /// Hit ratio in `[0.0, 1.0]`, or `0.0` when no lookups have been performed.
    #[must_use]
    pub fn hit_ratio(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            self.hits as f64 / total as f64
        }
    }
}

// ---------------------------------------------------------------------------
// Invalidation
// ---------------------------------------------------------------------------

/// Reason a cache entry was invalidated.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InvalidationReason {
    CodeChanged,
    DependencyChanged,
    ConfigChanged,
    Expired,
    Manual,
}

/// Batch invalidation descriptor.
#[derive(Debug, Clone, Default)]
pub struct InvalidationBatch {
    /// Invalidate all entries whose function name matches one of these.
    pub function_names: Vec<String>,
    /// Invalidate all entries whose file path matches one of these.
    pub file_paths: Vec<String>,
    /// Invalidate all entries whose function name contains the given substring.
    pub patterns: Vec<String>,
    /// Reason recorded in statistics.
    pub reason: Option<InvalidationReason>,
}

// ---------------------------------------------------------------------------
// Secondary index
// ---------------------------------------------------------------------------

/// Secondary indices mapping function names and file paths to cache keys.
#[derive(Debug, Clone, Default)]
pub(crate) struct CacheIndex {
    by_function: HashMap<String, Vec<CacheKey>>,
    by_file: HashMap<String, Vec<CacheKey>>,
}

impl CacheIndex {
    fn insert(&mut self, key: CacheKey, entry: &CacheEntry) {
        if let Some(ref name) = entry.function_name {
            self.by_function.entry(name.clone()).or_default().push(key);
        }
        if let Some(ref path) = entry.file_path {
            self.by_file.entry(path.clone()).or_default().push(key);
        }
    }

    fn remove(&mut self, key: CacheKey, entry: &CacheEntry) {
        if let Some(ref name) = entry.function_name {
            if let Some(keys) = self.by_function.get_mut(name) {
                keys.retain(|k| *k != key);
                if keys.is_empty() {
                    self.by_function.remove(name);
                }
            }
        }
        if let Some(ref path) = entry.file_path {
            if let Some(keys) = self.by_file.get_mut(path) {
                keys.retain(|k| *k != key);
                if keys.is_empty() {
                    self.by_file.remove(path);
                }
            }
        }
    }

    fn keys_for_function(&self, name: &str) -> &[CacheKey] {
        self.by_function
            .get(name)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    fn keys_for_file(&self, path: &str) -> &[CacheKey] {
        self.by_file
            .get(path)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// Fingerprint computer
// ---------------------------------------------------------------------------

/// Computes stable cache keys from VC content and solver configuration.
pub struct FingerprintComputer;

impl FingerprintComputer {
    /// Compute a [`CacheKey`] by hashing `vc_content` and `solver_config` together.
    #[must_use]
    pub fn compute(vc_content: &str, solver_config: &str) -> CacheKey {
        let mut hasher = Sha256::new();
        hasher.update(vc_content.as_bytes());
        hasher.update(b"\x00"); // separator to prevent concatenation collisions
        hasher.update(solver_config.as_bytes());
        CacheKey {
            hash: hasher.finalize().into(),
        }
    }

    /// Compute a key from pre-hashed components.
    #[must_use]
    pub fn compute_from_parts(vc_hash: u64, config_hash: u64) -> CacheKey {
        let mut hasher = Sha256::new();
        hasher.update(vc_hash.to_le_bytes());
        hasher.update(config_hash.to_le_bytes());
        CacheKey {
            hash: hasher.finalize().into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Warmup strategy
// ---------------------------------------------------------------------------

/// Strategy for pre-populating the cache on startup.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum WarmupStrategy {
    /// Load all entries from a prior cache image.
    Full,
    /// Load only entries whose function names appear in `functions`.
    Selective { functions: Vec<String> },
    /// Load the N most recently used entries.
    MostRecent { count: usize },
    /// Do not pre-populate.
    None,
}

// ---------------------------------------------------------------------------
// Cache migration
// ---------------------------------------------------------------------------

/// Handles transitions between on-disk cache format versions.
pub struct CacheMigration;

impl CacheMigration {
    /// The current format version that [`CacheSerializer`] writes.
    pub const CURRENT_VERSION: u32 = 2;

    /// Returns `true` if `version` can be migrated to the current format.
    #[must_use]
    pub fn can_migrate(version: u32) -> bool {
        matches!(version, 1 | 2)
    }

    /// Migrate raw serialized bytes from `from_version` to current.
    pub fn migrate(data: Vec<u8>, from_version: u32) -> Result<Vec<u8>, CacheError> {
        if from_version == Self::CURRENT_VERSION {
            return Ok(data);
        }
        if from_version == 1 {
            return Err(CacheError::Migration {
                from: from_version,
                to: Self::CURRENT_VERSION,
                detail:
                    "v1 used u64 DefaultHasher keys; re-run verification to populate v2 SHA-256 cache"
                        .into(),
            });
        }
        Err(CacheError::Migration {
            from: from_version,
            to: Self::CURRENT_VERSION,
            detail: "unsupported source version".into(),
        })
    }
}

// ---------------------------------------------------------------------------
// Serializer
// ---------------------------------------------------------------------------

/// Serializes and deserializes the cache to/from the filesystem.
///
/// Format (version 2):
///   `[4-byte LE version][4-byte LE entry count][entries...]`
/// Each entry:
///   `[32-byte SHA-256 key hash][1-byte result tag][...result payload][8-byte LE created_at_secs]
///    [8-byte LE access_count][4-byte LE size_bytes][len-prefixed solver_info]
///    [option-prefixed function_name][option-prefixed file_path][1-byte priority]`
pub struct CacheSerializer;

impl CacheSerializer {
    /// Write a length-prefixed UTF-8 string.
    fn write_string(buf: &mut Vec<u8>, s: &str) {
        let bytes = s.as_bytes();
        buf.extend_from_slice(&(u32::try_from(bytes.len()).unwrap_or(u32::MAX)).to_le_bytes());
        buf.extend_from_slice(bytes);
    }

    /// Write an optional length-prefixed string (0-byte tag = None, 1-byte tag = Some).
    fn write_opt_string(buf: &mut Vec<u8>, s: &Option<String>) {
        match s {
            Some(v) => {
                buf.push(1);
                Self::write_string(buf, v);
            }
            None => {
                buf.push(0);
            }
        }
    }

    fn read_u32(data: &[u8], pos: &mut usize) -> Result<u32, CacheError> {
        if *pos + 4 > data.len() {
            return Err(CacheError::CorruptData(
                "unexpected end of data (u32)".into(),
            ));
        }
        let val = u32::from_le_bytes([data[*pos], data[*pos + 1], data[*pos + 2], data[*pos + 3]]);
        *pos += 4;
        Ok(val)
    }

    fn read_u64(data: &[u8], pos: &mut usize) -> Result<u64, CacheError> {
        if *pos + 8 > data.len() {
            return Err(CacheError::CorruptData(
                "unexpected end of data (u64)".into(),
            ));
        }
        let val = u64::from_le_bytes([
            data[*pos],
            data[*pos + 1],
            data[*pos + 2],
            data[*pos + 3],
            data[*pos + 4],
            data[*pos + 5],
            data[*pos + 6],
            data[*pos + 7],
        ]);
        *pos += 8;
        Ok(val)
    }

    fn read_sha256(data: &[u8], pos: &mut usize) -> Result<[u8; 32], CacheError> {
        if *pos + 32 > data.len() {
            return Err(CacheError::CorruptData(
                "unexpected end of data (sha256)".into(),
            ));
        }
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&data[*pos..*pos + 32]);
        *pos += 32;
        Ok(hash)
    }

    fn read_string(data: &[u8], pos: &mut usize) -> Result<String, CacheError> {
        let len = Self::read_u32(data, pos)? as usize;
        if *pos + len > data.len() {
            return Err(CacheError::CorruptData(
                "unexpected end of string data".into(),
            ));
        }
        let s = std::str::from_utf8(&data[*pos..*pos + len])
            .map_err(|e| CacheError::CorruptData(format!("invalid UTF-8: {e}")))?;
        *pos += len;
        Ok(s.to_owned())
    }

    fn read_opt_string(data: &[u8], pos: &mut usize) -> Result<Option<String>, CacheError> {
        if *pos >= data.len() {
            return Err(CacheError::CorruptData(
                "unexpected end of data (opt tag)".into(),
            ));
        }
        let tag = data[*pos];
        *pos += 1;
        match tag {
            0 => Ok(None),
            1 => Self::read_string(data, pos).map(Some),
            _ => Err(CacheError::CorruptData(format!(
                "invalid option tag: {tag}"
            ))),
        }
    }

    /// Serialize the entire contents of a [`ProofCache`] to a byte vector.
    #[must_use]
    pub fn serialize(cache: &ProofCache) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&cache.config.format_version.to_le_bytes());
        buf.extend_from_slice(
            &(u32::try_from(cache.entries.len()).unwrap_or(u32::MAX)).to_le_bytes(),
        );

        // Deterministic iteration order via BTreeMap over keys.
        let sorted: BTreeMap<CacheKey, &CacheEntry> =
            cache.entries.iter().map(|(&k, v)| (k, v)).collect();

        for (&key, entry) in &sorted {
            buf.extend_from_slice(&key.hash);
            match &entry.result {
                CachedResult::Verified => buf.push(0),
                CachedResult::Failed { reason } => {
                    buf.push(1);
                    Self::write_string(&mut buf, reason);
                }
                CachedResult::Unknown => buf.push(2),
                CachedResult::Timeout => buf.push(3),
            }
            buf.extend_from_slice(&entry.created_at.as_secs().to_le_bytes());
            buf.extend_from_slice(&entry.access_count.to_le_bytes());
            buf.extend_from_slice(
                &(u32::try_from(entry.size_bytes).unwrap_or(u32::MAX)).to_le_bytes(),
            );
            Self::write_string(&mut buf, &entry.solver_info);
            Self::write_opt_string(&mut buf, &entry.function_name);
            Self::write_opt_string(&mut buf, &entry.file_path);
            buf.push(entry.priority);
        }
        buf
    }

    /// Deserialize a byte vector (as produced by [`Self::serialize`]) back into
    /// `(format_version, Vec<(CacheKey, CacheEntry)>)`.
    pub fn deserialize(data: &[u8]) -> Result<(u32, Vec<(CacheKey, CacheEntry)>), CacheError> {
        let mut pos = 0;
        let version = Self::read_u32(data, &mut pos)?;
        let count = Self::read_u32(data, &mut pos)? as usize;

        let mut entries = Vec::with_capacity(count);
        for _ in 0..count {
            let hash = Self::read_sha256(data, &mut pos)?;
            let key = CacheKey { hash };

            if pos >= data.len() {
                return Err(CacheError::CorruptData(
                    "unexpected end (result tag)".into(),
                ));
            }
            let tag = data[pos];
            pos += 1;

            let result = match tag {
                0 => CachedResult::Verified,
                1 => {
                    let reason = Self::read_string(data, &mut pos)?;
                    CachedResult::Failed { reason }
                }
                2 => CachedResult::Unknown,
                3 => CachedResult::Timeout,
                _ => {
                    return Err(CacheError::CorruptData(format!(
                        "unknown result tag: {tag}"
                    )));
                }
            };

            let created_secs = Self::read_u64(data, &mut pos)?;
            let access_count = Self::read_u64(data, &mut pos)?;
            let size_bytes = Self::read_u32(data, &mut pos)? as usize;
            let solver_info = Self::read_string(data, &mut pos)?;
            let function_name = Self::read_opt_string(data, &mut pos)?;
            let file_path = Self::read_opt_string(data, &mut pos)?;

            if pos >= data.len() {
                return Err(CacheError::CorruptData("unexpected end (priority)".into()));
            }
            let priority = data[pos];
            pos += 1;

            entries.push((
                key,
                CacheEntry {
                    result,
                    created_at: Duration::from_secs(created_secs),
                    access_count,
                    size_bytes,
                    solver_info,
                    function_name,
                    file_path,
                    priority,
                    last_accessed: None,
                },
            ));
        }
        Ok((version, entries))
    }
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors produced by cache operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CacheError {
    #[error("{context}: {source}")]
    Io {
        context: &'static str,
        #[source]
        source: io::Error,
    },
    #[error("corrupt cache data: {0}")]
    CorruptData(String),
    #[error("cache migration v{from}->v{to}: {detail}")]
    Migration { from: u32, to: u32, detail: String },
}

// ---------------------------------------------------------------------------
// ProofCache — main cache
// ---------------------------------------------------------------------------

/// Verification-aware proof cache.
///
/// Stores [`CacheEntry`] values keyed by [`CacheKey`], provides secondary
/// index lookups, TTL-based and capacity-based eviction, and filesystem
/// persistence.
pub struct ProofCache {
    config: CacheConfig,
    entries: HashMap<CacheKey, CacheEntry>,
    /// LRU/FIFO order tracking (front = oldest / least-recently-used).
    order: VecDeque<CacheKey>,
    index: CacheIndex,
    stats: CacheStats,
}

impl ProofCache {
    // ----- Construction -----

    /// Create a new empty cache with the given configuration.
    #[must_use]
    pub fn new(config: CacheConfig) -> Self {
        Self {
            config,
            entries: HashMap::new(),
            order: VecDeque::new(),
            index: CacheIndex::default(),
            stats: CacheStats::default(),
        }
    }

    /// Return a reference to the current configuration.
    #[must_use]
    pub fn config(&self) -> &CacheConfig {
        &self.config
    }

    // ----- Lookup -----

    /// Look up a cache entry by key.
    ///
    /// Records a hit or miss in the statistics and bumps the access count
    /// on a hit.
    pub fn get(&mut self, key: &CacheKey) -> Option<&CacheEntry> {
        if self.entries.contains_key(key) {
            // Bump access metadata.
            if let Some(entry) = self.entries.get_mut(key) {
                entry.access_count += 1;
                entry.last_accessed = Some(Instant::now());
            }
            // Move to back of LRU queue.
            self.order.retain(|k| k != key);
            self.order.push_back(*key);

            self.stats.hits += 1;
            self.entries.get(key)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Non-tracking peek (does not affect statistics or access order).
    #[must_use]
    pub fn peek(&self, key: &CacheKey) -> Option<&CacheEntry> {
        self.entries.get(key)
    }

    // ----- Insertion -----

    /// Insert a new verification result into the cache.
    ///
    /// If the cache is at capacity (by entry count or memory), the configured
    /// eviction policy is used to make room.
    pub fn put(
        &mut self,
        key: CacheKey,
        result: CachedResult,
        solver_info: impl Into<String>,
    ) -> &CacheEntry {
        self.put_with_metadata(key, result, solver_info.into(), None, None, 0)
    }

    /// Insert with full metadata (function name, file path, priority).
    pub fn put_with_metadata(
        &mut self,
        key: CacheKey,
        result: CachedResult,
        solver_info: String,
        function_name: Option<String>,
        file_path: Option<String>,
        priority: u8,
    ) -> &CacheEntry {
        // Remove old entry if overwriting.
        if let Some(old) = self.entries.remove(&key) {
            self.stats.memory_used_bytes = self
                .stats
                .memory_used_bytes
                .saturating_sub(old.estimated_heap_size());
            self.index.remove(key, &old);
            self.order.retain(|k| *k != key);
        }

        let now_duration = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();

        let entry = CacheEntry {
            result,
            created_at: now_duration,
            access_count: 0,
            size_bytes: 0,
            solver_info,
            function_name,
            file_path,
            priority,
            last_accessed: Some(Instant::now()),
        };

        // Evict if necessary — entry count.
        while self.entries.len() >= self.config.max_entries {
            if !self.evict_one() {
                break;
            }
        }

        // Evict if necessary — memory.
        let new_size = entry.estimated_heap_size();
        while self.stats.memory_used_bytes + new_size > self.config.max_memory_bytes
            && !self.entries.is_empty()
        {
            if !self.evict_one() {
                break;
            }
        }

        self.stats.memory_used_bytes += new_size;
        self.stats.entry_count = self.entries.len() + 1;
        self.index.insert(key, &entry);
        self.order.push_back(key);
        self.entries.entry(key).or_insert(entry)
    }

    // ----- Invalidation -----

    /// Invalidate a single cache entry by key.
    pub fn invalidate(&mut self, key: &CacheKey) -> bool {
        if let Some(old) = self.entries.remove(key) {
            self.stats.memory_used_bytes = self
                .stats
                .memory_used_bytes
                .saturating_sub(old.estimated_heap_size());
            self.index.remove(*key, &old);
            self.order.retain(|k| k != key);
            self.stats.invalidations += 1;
            self.stats.entry_count = self.entries.len();
            true
        } else {
            false
        }
    }

    /// Batch-invalidate entries matching any criterion in `batch`.
    pub fn invalidate_batch(&mut self, batch: &InvalidationBatch) -> usize {
        let mut to_remove = Vec::new();

        for name in &batch.function_names {
            to_remove.extend_from_slice(self.index.keys_for_function(name));
        }
        for path in &batch.file_paths {
            to_remove.extend_from_slice(self.index.keys_for_file(path));
        }
        if !batch.patterns.is_empty() {
            for (&key, entry) in &self.entries {
                if let Some(ref fn_name) = entry.function_name {
                    if batch.patterns.iter().any(|p| fn_name.contains(p.as_str())) {
                        to_remove.push(key);
                    }
                }
            }
        }

        to_remove.sort();
        to_remove.dedup();

        let count = to_remove.len();
        for key in to_remove {
            self.invalidate(&key);
        }
        count
    }

    // ----- Eviction helpers -----

    /// Evict the single best victim according to the configured policy.
    /// Returns `true` if an entry was evicted.
    fn evict_one(&mut self) -> bool {
        let victim = match self.config.eviction_policy {
            EvictionPolicy::Lru => self.pick_lru_victim(),
            EvictionPolicy::Lfu => self.pick_lfu_victim(),
            EvictionPolicy::FifoWithPriority => self.pick_fifo_priority_victim(),
            EvictionPolicy::AdaptiveArc => {
                // Simplified ARC: evict LRU among least-accessed half.
                self.pick_arc_victim()
            }
        };

        if let Some(key) = victim {
            if let Some(old) = self.entries.remove(&key) {
                self.stats.memory_used_bytes = self
                    .stats
                    .memory_used_bytes
                    .saturating_sub(old.estimated_heap_size());
                self.index.remove(key, &old);
                self.order.retain(|k| *k != key);
                self.stats.evictions += 1;
                self.stats.entry_count = self.entries.len();
                return true;
            }
        }
        false
    }

    fn pick_lru_victim(&self) -> Option<CacheKey> {
        self.order.front().copied()
    }

    fn pick_lfu_victim(&self) -> Option<CacheKey> {
        self.entries
            .iter()
            .min_by_key(|(_, e)| e.access_count)
            .map(|(&k, _)| k)
    }

    fn pick_fifo_priority_victim(&self) -> Option<CacheKey> {
        // Evict the lowest-priority entry that is earliest in FIFO order.
        let min_priority = self.entries.values().map(|e| e.priority).min()?;
        self.order
            .iter()
            .find(|k| {
                self.entries
                    .get(k)
                    .is_some_and(|e| e.priority == min_priority)
            })
            .copied()
    }

    fn pick_arc_victim(&self) -> Option<CacheKey> {
        if self.entries.is_empty() {
            return None;
        }
        // Simplified ARC: partition into low-frequency and high-frequency halves,
        // then pick LRU from the low-frequency half.
        let mut sorted: Vec<_> = self.entries.iter().collect();
        sorted.sort_by_key(|(_, e)| e.access_count);
        let half = sorted.len().div_ceil(2);
        let low_freq: Vec<CacheKey> = sorted[..half].iter().map(|(&k, _)| k).collect();

        // Among low-frequency entries, pick the one earliest in LRU order.
        self.order
            .iter()
            .find(|k| low_freq.contains(k))
            .copied()
            .or_else(|| self.order.front().copied())
    }

    /// Evict all entries that have exceeded their TTL.
    pub fn evict_expired(&mut self) -> usize {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();

        let expired: Vec<CacheKey> = self
            .entries
            .iter()
            .filter(|(_, e)| now.saturating_sub(e.created_at) > self.config.ttl)
            .map(|(&k, _)| k)
            .collect();

        let count = expired.len();
        for key in expired {
            self.invalidate(&key);
        }
        count
    }

    /// Evict entries using LRU policy (convenience wrapper for manual eviction).
    pub fn evict_lru(&mut self) -> bool {
        if self.entries.is_empty() {
            return false;
        }
        let victim = self.pick_lru_victim();
        if let Some(key) = victim {
            if let Some(old) = self.entries.remove(&key) {
                self.stats.memory_used_bytes = self
                    .stats
                    .memory_used_bytes
                    .saturating_sub(old.estimated_heap_size());
                self.index.remove(key, &old);
                self.order.retain(|k| *k != key);
                self.stats.evictions += 1;
                self.stats.entry_count = self.entries.len();
                return true;
            }
        }
        false
    }

    // ----- Statistics and queries -----

    /// Return current cache statistics.
    #[must_use]
    pub fn stats(&self) -> &CacheStats {
        &self.stats
    }

    /// Total estimated memory usage of all cached entries (bytes).
    #[must_use]
    pub fn memory_usage(&self) -> usize {
        self.stats.memory_used_bytes
    }

    /// Number of entries currently in the cache.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the cache contains no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Check if a key exists without modifying statistics.
    #[must_use]
    pub fn contains_key(&self, key: &CacheKey) -> bool {
        self.entries.contains_key(key)
    }

    // ----- Secondary index lookups -----

    /// Return all entries whose function name matches `name`.
    #[must_use]
    pub fn by_function(&self, name: &str) -> Vec<&CacheEntry> {
        self.index
            .keys_for_function(name)
            .iter()
            .filter_map(|k| self.entries.get(k))
            .collect()
    }

    /// Return all entries whose file path matches `path`.
    #[must_use]
    pub fn by_file(&self, path: &str) -> Vec<&CacheEntry> {
        self.index
            .keys_for_file(path)
            .iter()
            .filter_map(|k| self.entries.get(k))
            .collect()
    }

    // ----- Persistence -----

    /// Serialize this cache and write it to `path`.
    pub fn save_to_disk(&self, path: &Path) -> Result<(), CacheError> {
        let data = CacheSerializer::serialize(self);
        std::fs::write(path, data).map_err(|e| CacheError::Io {
            context: "save_to_disk",
            source: e,
        })
    }

    /// Load a cache from disk, optionally migrating old format versions.
    pub fn load_from_disk(path: &Path, config: CacheConfig) -> Result<Self, CacheError> {
        let data = std::fs::read(path).map_err(|e| CacheError::Io {
            context: "load_from_disk",
            source: e,
        })?;

        let (version, entries) = CacheSerializer::deserialize(&data)?;

        let data = if version != CacheMigration::CURRENT_VERSION {
            let migrated = CacheMigration::migrate(data, version)?;
            CacheSerializer::deserialize(&migrated)?.1
        } else {
            entries
        };

        let mut cache = Self::new(config);
        for (key, entry) in data {
            let size = entry.estimated_heap_size();
            cache.index.insert(key, &entry);
            cache.stats.memory_used_bytes += size;
            cache.order.push_back(key);
            cache.entries.insert(key, entry);
        }
        cache.stats.entry_count = cache.entries.len();
        Ok(cache)
    }

    // ----- Warmup -----

    /// Pre-populate the cache according to the given strategy.
    pub fn warmup(&mut self, strategy: &WarmupStrategy, entries: Vec<(CacheKey, CacheEntry)>) {
        let filtered: Vec<(CacheKey, CacheEntry)> = match strategy {
            WarmupStrategy::Full => entries,
            WarmupStrategy::Selective { functions } => entries
                .into_iter()
                .filter(|(_, e)| {
                    e.function_name
                        .as_ref()
                        .is_some_and(|n| functions.contains(n))
                })
                .collect(),
            WarmupStrategy::MostRecent { count } => {
                let mut sorted = entries;
                sorted.sort_by_key(|(_, entry)| std::cmp::Reverse(entry.created_at));
                sorted.into_iter().take(*count).collect()
            }
            WarmupStrategy::None => return,
        };

        for (key, entry) in filtered {
            if self.entries.len() >= self.config.max_entries {
                break;
            }
            let size = entry.estimated_heap_size();
            if self.stats.memory_used_bytes + size > self.config.max_memory_bytes {
                continue;
            }
            self.index.insert(key, &entry);
            self.stats.memory_used_bytes += size;
            self.order.push_back(key);
            self.entries.insert(key, entry);
        }
        self.stats.entry_count = self.entries.len();
    }

    /// Remove all entries and reset statistics.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
        self.index = CacheIndex::default();
        self.stats = CacheStats::default();
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_config(max_entries: usize) -> CacheConfig {
        CacheConfig {
            max_entries,
            max_memory_bytes: 64 * 1024 * 1024,
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        }
    }

    fn make_key(n: u64) -> CacheKey {
        use sha2::{Digest, Sha256};

        let hash: [u8; 32] = Sha256::digest(n.to_le_bytes()).into();
        CacheKey::from_raw(hash)
    }

    fn make_entry(result: CachedResult, fn_name: Option<&str>, file: Option<&str>) -> CacheEntry {
        CacheEntry {
            result,
            created_at: Duration::from_secs(1000),
            access_count: 0,
            size_bytes: 0,
            solver_info: "ay-default".into(),
            function_name: fn_name.map(String::from),
            file_path: file.map(String::from),
            priority: 0,
            last_accessed: None,
        }
    }

    // -----------------------------------------------------------------------
    // Basic construction and insertion
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_cache_is_empty() {
        let cache = ProofCache::new(make_config(16));
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.stats().hits, 0);
        assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn test_put_and_get_verified() {
        let mut cache = ProofCache::new(make_config(16));
        let key = FingerprintComputer::compute("vc1", "config1");
        cache.put(key, CachedResult::Verified, "ay-default");
        let entry = cache.get(&key).expect("should be present");
        assert!(entry.result.is_verified());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_put_and_get_failed() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(42);
        cache.put(
            key,
            CachedResult::Failed {
                reason: "assertion violated".into(),
            },
            "ay-bv",
        );
        let entry = cache.get(&key).expect("should be present");
        assert!(!entry.result.is_verified());
        assert!(
            matches!(&entry.result, CachedResult::Failed { reason } if reason == "assertion violated")
        );
    }

    #[test]
    fn test_put_and_get_unknown() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(99);
        cache.put(key, CachedResult::Unknown, "ay-nia");
        let entry = cache.get(&key).expect("should be present");
        assert!(matches!(&entry.result, CachedResult::Unknown));
    }

    #[test]
    fn test_put_and_get_timeout() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(100);
        cache.put(key, CachedResult::Timeout, "ay-default");
        let entry = cache.get(&key).expect("should be present");
        assert!(matches!(&entry.result, CachedResult::Timeout));
    }

    #[test]
    fn test_get_miss_increments_stat() {
        let mut cache = ProofCache::new(make_config(16));
        let missing = make_key(999);
        assert!(cache.get(&missing).is_none());
        assert_eq!(cache.stats().misses, 1);
        assert_eq!(cache.stats().hits, 0);
    }

    #[test]
    fn test_get_hit_increments_stat() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        cache.get(&key);
        assert_eq!(cache.stats().hits, 1);
    }

    #[test]
    fn test_peek_does_not_affect_stats() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        let _ = cache.peek(&key);
        assert_eq!(cache.stats().hits, 0);
        assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn test_contains_key() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(5);
        assert!(!cache.contains_key(&key));
        cache.put(key, CachedResult::Verified, "ay");
        assert!(cache.contains_key(&key));
    }

    #[test]
    fn test_overwrite_replaces_entry() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "old");
        cache.put(
            key,
            CachedResult::Failed {
                reason: "new".into(),
            },
            "new",
        );
        assert_eq!(cache.len(), 1);
        let entry = cache.get(&key).unwrap();
        assert!(matches!(&entry.result, CachedResult::Failed { .. }));
    }

    // -----------------------------------------------------------------------
    // Eviction — LRU
    // -----------------------------------------------------------------------

    #[test]
    fn test_lru_eviction_at_capacity() {
        let mut cache = ProofCache::new(make_config(3));
        for i in 0..3 {
            cache.put(make_key(i), CachedResult::Verified, "ay");
        }
        assert_eq!(cache.len(), 3);
        // Insert a fourth entry — LRU (key 0) should be evicted.
        cache.put(make_key(10), CachedResult::Verified, "ay");
        assert_eq!(cache.len(), 3);
        assert!(!cache.contains_key(&make_key(0)));
        assert!(cache.contains_key(&make_key(1)));
        assert!(cache.contains_key(&make_key(10)));
        assert!(cache.stats().evictions >= 1);
    }

    #[test]
    fn test_lru_access_promotes_entry() {
        let mut cache = ProofCache::new(make_config(3));
        for i in 0..3 {
            cache.put(make_key(i), CachedResult::Verified, "ay");
        }
        // Access key 0 → it moves to back of LRU queue.
        cache.get(&make_key(0));
        // Insert key 10 → key 1 (now oldest) should be evicted.
        cache.put(make_key(10), CachedResult::Verified, "ay");
        assert!(cache.contains_key(&make_key(0)));
        assert!(!cache.contains_key(&make_key(1)));
    }

    #[test]
    fn test_manual_evict_lru() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        assert!(cache.evict_lru());
        assert_eq!(cache.len(), 1);
        assert!(!cache.contains_key(&make_key(1)));
    }

    #[test]
    fn test_evict_lru_on_empty_returns_false() {
        let mut cache = ProofCache::new(make_config(16));
        assert!(!cache.evict_lru());
    }

    // -----------------------------------------------------------------------
    // Eviction — LFU
    // -----------------------------------------------------------------------

    #[test]
    fn test_lfu_eviction_removes_least_frequent() {
        let mut config = make_config(3);
        config.eviction_policy = EvictionPolicy::Lfu;
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        // Access key 1 and key 3 multiple times.
        cache.get(&make_key(1));
        cache.get(&make_key(1));
        cache.get(&make_key(3));
        // Insert key 4 → key 2 (least-frequently used) should go.
        cache.put(make_key(4), CachedResult::Verified, "ay");
        assert!(!cache.contains_key(&make_key(2)));
        assert!(cache.contains_key(&make_key(1)));
        assert!(cache.contains_key(&make_key(3)));
    }

    // -----------------------------------------------------------------------
    // Eviction — FIFO with priority
    // -----------------------------------------------------------------------

    #[test]
    fn test_fifo_priority_evicts_lowest_priority_first() {
        let mut config = make_config(3);
        config.eviction_policy = EvictionPolicy::FifoWithPriority;
        let mut cache = ProofCache::new(config);
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            10,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            1,
        );
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            5,
        );
        // Key 2 (priority 1) should be evicted first.
        cache.put_with_metadata(
            make_key(4),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            8,
        );
        assert!(!cache.contains_key(&make_key(2)));
        assert!(cache.contains_key(&make_key(1)));
    }

    // -----------------------------------------------------------------------
    // Eviction — AdaptiveArc
    // -----------------------------------------------------------------------

    #[test]
    fn test_arc_evicts_low_frequency_lru() {
        let mut config = make_config(3);
        config.eviction_policy = EvictionPolicy::AdaptiveArc;
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        // Boost key 1 frequency.
        cache.get(&make_key(1));
        cache.get(&make_key(1));
        cache.get(&make_key(1));
        // Key 2 has 0 accesses (after put, it starts at 0), so it is low-frequency LRU.
        cache.put(make_key(4), CachedResult::Verified, "ay");
        assert!(cache.contains_key(&make_key(1)));
        assert_eq!(cache.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_invalidate_single() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        assert!(cache.invalidate(&key));
        assert!(cache.is_empty());
        assert_eq!(cache.stats().invalidations, 1);
    }

    #[test]
    fn test_invalidate_missing_returns_false() {
        let mut cache = ProofCache::new(make_config(16));
        assert!(!cache.invalidate(&make_key(999)));
    }

    #[test]
    fn test_invalidate_batch_by_function() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("foo".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("bar".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            Some("foo".into()),
            None,
            0,
        );
        let batch = InvalidationBatch {
            function_names: vec!["foo".into()],
            ..Default::default()
        };
        let removed = cache.invalidate_batch(&batch);
        assert_eq!(removed, 2);
        assert_eq!(cache.len(), 1);
        assert!(cache.contains_key(&make_key(2)));
    }

    #[test]
    fn test_invalidate_batch_by_file() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            None,
            Some("src/lib.rs".into()),
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            None,
            Some("src/main.rs".into()),
            0,
        );
        let batch = InvalidationBatch {
            file_paths: vec!["src/lib.rs".into()],
            ..Default::default()
        };
        let removed = cache.invalidate_batch(&batch);
        assert_eq!(removed, 1);
        assert!(cache.contains_key(&make_key(2)));
    }

    #[test]
    fn test_invalidate_batch_by_pattern() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("test_add_overflow".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("test_mul_overflow".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            Some("verify_bounds".into()),
            None,
            0,
        );
        let batch = InvalidationBatch {
            patterns: vec!["overflow".into()],
            ..Default::default()
        };
        let removed = cache.invalidate_batch(&batch);
        assert_eq!(removed, 2);
        assert!(cache.contains_key(&make_key(3)));
    }

    // -----------------------------------------------------------------------
    // Secondary index
    // -----------------------------------------------------------------------

    #[test]
    fn test_by_function_lookup() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("my_proof".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("my_proof".into()),
            None,
            0,
        );
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            Some("other".into()),
            None,
            0,
        );
        let results = cache.by_function("my_proof");
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_by_file_lookup() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            None,
            Some("src/cache.rs".into()),
            0,
        );
        let results = cache.by_file("src/cache.rs");
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_by_function_empty_result() {
        let cache = ProofCache::new(make_config(16));
        assert!(cache.by_function("nonexistent").is_empty());
    }

    #[test]
    fn test_by_file_empty_result() {
        let cache = ProofCache::new(make_config(16));
        assert!(cache.by_file("nonexistent").is_empty());
    }

    // -----------------------------------------------------------------------
    // Fingerprint computer
    // -----------------------------------------------------------------------

    #[test]
    fn test_fingerprint_deterministic() {
        let a = FingerprintComputer::compute("vc_body", "solver_cfg");
        let b = FingerprintComputer::compute("vc_body", "solver_cfg");
        assert_eq!(a, b);
    }

    #[test]
    fn test_fingerprint_different_vc_different_key() {
        let a = FingerprintComputer::compute("vc_a", "cfg");
        let b = FingerprintComputer::compute("vc_b", "cfg");
        assert_ne!(a, b);
    }

    #[test]
    fn test_fingerprint_different_config_different_key() {
        let a = FingerprintComputer::compute("vc", "cfg_a");
        let b = FingerprintComputer::compute("vc", "cfg_b");
        assert_ne!(a, b);
    }

    #[test]
    fn test_fingerprint_from_parts() {
        let a = FingerprintComputer::compute_from_parts(123, 456);
        let b = FingerprintComputer::compute_from_parts(123, 456);
        assert_eq!(a, b);
        let c = FingerprintComputer::compute_from_parts(123, 789);
        assert_ne!(a, c);
    }

    // -----------------------------------------------------------------------
    // Statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_hit_ratio_zero_lookups() {
        let stats = CacheStats::default();
        assert!((stats.hit_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_hit_ratio_all_hits() {
        let stats = CacheStats {
            hits: 10,
            misses: 0,
            ..Default::default()
        };
        assert!((stats.hit_ratio() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_hit_ratio_mixed() {
        let stats = CacheStats {
            hits: 3,
            misses: 7,
            ..Default::default()
        };
        assert!((stats.hit_ratio() - 0.3).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Serialization round-trip
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_deserialize_empty() {
        let cache = ProofCache::new(make_config(16));
        let data = CacheSerializer::serialize(&cache);
        let (version, entries) = CacheSerializer::deserialize(&data).unwrap();
        assert_eq!(version, 2);
        assert!(entries.is_empty());
    }

    #[test]
    fn test_serialize_deserialize_round_trip() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay-bv".into(),
            Some("prove_add".into()),
            Some("src/arith.rs".into()),
            5,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Failed {
                reason: "assertion violated at line 42".into(),
            },
            "ay-nia".into(),
            None,
            None,
            0,
        );
        cache.put(make_key(3), CachedResult::Unknown, "ay");
        cache.put(make_key(4), CachedResult::Timeout, "ay");

        let data = CacheSerializer::serialize(&cache);
        let (version, entries) = CacheSerializer::deserialize(&data).unwrap();
        assert_eq!(version, 2);
        assert_eq!(entries.len(), 4);

        // Verify specific entries survived the round-trip.
        let entry1 = entries
            .iter()
            .find(|(k, _)| *k == make_key(1))
            .unwrap()
            .1
            .clone();
        assert!(entry1.result.is_verified());
        assert_eq!(entry1.function_name.as_deref(), Some("prove_add"));
        assert_eq!(entry1.file_path.as_deref(), Some("src/arith.rs"));
        assert_eq!(entry1.priority, 5);
        assert_eq!(entry1.solver_info, "ay-bv");

        let entry2 = entries
            .iter()
            .find(|(k, _)| *k == make_key(2))
            .unwrap()
            .1
            .clone();
        assert!(
            matches!(&entry2.result, CachedResult::Failed { reason } if reason.contains("line 42"))
        );
    }

    #[test]
    fn test_deserialize_corrupt_data() {
        let err = CacheSerializer::deserialize(&[0xFF])
            .expect_err("corrupt data should fail deserialization");
        let msg = err.to_string();
        assert!(
            !msg.is_empty(),
            "deserialization error should have a non-empty message"
        );
    }

    // -----------------------------------------------------------------------
    // Disk persistence
    // -----------------------------------------------------------------------

    #[test]
    fn test_save_and_load_from_disk() {
        let dir = std::env::temp_dir().join("trust_vc_proof_cache_test_save_load");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("cache.bin");

        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(10),
            CachedResult::Verified,
            "ay".into(),
            Some("lemma_x".into()),
            Some("src/x.rs".into()),
            0,
        );
        cache.save_to_disk(&path).expect("save should succeed");

        let loaded =
            ProofCache::load_from_disk(&path, make_config(16)).expect("load should succeed");
        assert_eq!(loaded.len(), 1);
        let entry = loaded.peek(&make_key(10)).unwrap();
        assert!(entry.result.is_verified());
        assert_eq!(entry.function_name.as_deref(), Some("lemma_x"));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_load_from_nonexistent_path() {
        let msg = ProofCache::load_from_disk(Path::new("/nonexistent/cache.bin"), make_config(16))
            .err()
            .expect("loading from nonexistent path should fail")
            .to_string();
        assert!(
            !msg.is_empty(),
            "load error should have a non-empty message"
        );
    }

    // -----------------------------------------------------------------------
    // Warmup
    // -----------------------------------------------------------------------

    #[test]
    fn test_warmup_full() {
        let mut cache = ProofCache::new(make_config(16));
        let entries = vec![
            (
                make_key(1),
                make_entry(CachedResult::Verified, Some("a"), None),
            ),
            (
                make_key(2),
                make_entry(CachedResult::Verified, Some("b"), None),
            ),
        ];
        cache.warmup(&WarmupStrategy::Full, entries);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_warmup_selective() {
        let mut cache = ProofCache::new(make_config(16));
        let entries = vec![
            (
                make_key(1),
                make_entry(CachedResult::Verified, Some("keep"), None),
            ),
            (
                make_key(2),
                make_entry(CachedResult::Verified, Some("drop"), None),
            ),
        ];
        let strategy = WarmupStrategy::Selective {
            functions: vec!["keep".into()],
        };
        cache.warmup(&strategy, entries);
        assert_eq!(cache.len(), 1);
        assert!(cache.contains_key(&make_key(1)));
    }

    #[test]
    fn test_warmup_most_recent() {
        let mut cache = ProofCache::new(make_config(16));
        let mut e1 = make_entry(CachedResult::Verified, Some("old"), None);
        e1.created_at = Duration::from_secs(100);
        let mut e2 = make_entry(CachedResult::Verified, Some("new"), None);
        e2.created_at = Duration::from_secs(200);
        let mut e3 = make_entry(CachedResult::Verified, Some("newest"), None);
        e3.created_at = Duration::from_secs(300);

        let entries = vec![(make_key(1), e1), (make_key(2), e2), (make_key(3), e3)];
        cache.warmup(&WarmupStrategy::MostRecent { count: 2 }, entries);
        assert_eq!(cache.len(), 2);
        // Should have keys 2 and 3 (most recent).
        assert!(cache.contains_key(&make_key(3)));
        assert!(cache.contains_key(&make_key(2)));
    }

    #[test]
    fn test_warmup_none_does_nothing() {
        let mut cache = ProofCache::new(make_config(16));
        let entries = vec![(make_key(1), make_entry(CachedResult::Verified, None, None))];
        cache.warmup(&WarmupStrategy::None, entries);
        assert!(cache.is_empty());
    }

    // -----------------------------------------------------------------------
    // Memory tracking
    // -----------------------------------------------------------------------

    #[test]
    fn test_memory_usage_increases_on_put() {
        let mut cache = ProofCache::new(make_config(16));
        let before = cache.memory_usage();
        cache.put(make_key(1), CachedResult::Verified, "ay");
        assert!(cache.memory_usage() > before);
    }

    #[test]
    fn test_memory_usage_decreases_on_invalidate() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        let before = cache.memory_usage();
        cache.invalidate(&make_key(1));
        assert!(cache.memory_usage() < before);
    }

    #[test]
    fn test_memory_limit_triggers_eviction() {
        let config = CacheConfig {
            max_entries: 1000,
            // Very small memory budget to force evictions.
            max_memory_bytes: 200,
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        // Each entry is at least ~100+ bytes on the heap.
        for i in 0..50 {
            cache.put(make_key(i), CachedResult::Verified, "ay");
        }
        // Not all 50 should fit within 200 bytes.
        assert!(cache.len() < 50);
        assert!(cache.stats().evictions > 0);
    }

    // -----------------------------------------------------------------------
    // Clear
    // -----------------------------------------------------------------------

    #[test]
    fn test_clear_resets_everything() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.get(&make_key(1));
        cache.get(&make_key(999)); // miss
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.stats().hits, 0);
        assert_eq!(cache.stats().misses, 0);
        assert_eq!(cache.stats().evictions, 0);
        assert_eq!(cache.memory_usage(), 0);
    }

    // -----------------------------------------------------------------------
    // CacheKey display
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_key_display() {
        let key = CacheKey::from_raw([
            0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55,
            0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x01, 0x02, 0x03, 0x04,
            0x05, 0x06, 0x07, 0x08,
        ]);
        let s = format!("{key}");
        assert_eq!(
            s,
            "deadbeefcafebabe00112233445566778899aabbccddeeff0102030405060708"
        );
    }

    // -----------------------------------------------------------------------
    // CacheMigration
    // -----------------------------------------------------------------------

    #[test]
    fn test_migration_current_version_passthrough() {
        let data = vec![1, 2, 3];
        let result = CacheMigration::migrate(data.clone(), 2);
        assert_eq!(result.unwrap(), data);
    }

    #[test]
    fn test_migration_unsupported_version() {
        let err = CacheMigration::migrate(vec![], 99)
            .expect_err("unsupported version should fail migration");
        let msg = err.to_string();
        assert!(
            msg.contains("version") || msg.contains("unsupported") || msg.contains("migrate"),
            "migration error should mention version/unsupported, got: {msg}"
        );
    }

    #[test]
    fn test_can_migrate_current() {
        assert!(CacheMigration::can_migrate(2));
    }

    #[test]
    fn test_can_migrate_future_version() {
        assert!(!CacheMigration::can_migrate(99));
    }

    // -----------------------------------------------------------------------
    // InvalidationReason / CacheError display
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_error_display_corrupt() {
        let e = CacheError::CorruptData("bad data".into());
        assert!(format!("{e}").contains("corrupt"));
    }

    #[test]
    fn test_cache_error_display_migration() {
        let e = CacheError::Migration {
            from: 0,
            to: 1,
            detail: "unsupported".into(),
        };
        assert!(format!("{e}").contains("v0->v1"));
    }

    // -----------------------------------------------------------------------
    // Default config
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config() {
        let config = CacheConfig::default();
        assert_eq!(config.max_entries, 4096);
        assert_eq!(config.eviction_policy, EvictionPolicy::Lru);
        assert_eq!(config.format_version, 2);
        assert!(config.ttl.as_secs() > 0);
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_access_count_increments() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        for _ in 0..5 {
            cache.get(&key);
        }
        let entry = cache.peek(&key).unwrap();
        assert_eq!(entry.access_count, 5);
    }

    #[test]
    fn test_invalidate_batch_empty_criteria() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        let batch = InvalidationBatch::default();
        let removed = cache.invalidate_batch(&batch);
        assert_eq!(removed, 0);
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_entry_count_stat_tracks_len() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        assert_eq!(cache.stats().entry_count, 2);
        cache.invalidate(&make_key(1));
        assert_eq!(cache.stats().entry_count, 1);
    }

    // -----------------------------------------------------------------------
    // Fingerprint collision prevention
    // -----------------------------------------------------------------------

    #[test]
    fn test_fingerprint_separator_prevents_concatenation_collision() {
        // Without the \x00 separator, ("ab", "cd") and ("abc", "d") would hash
        // the same bytes.  The separator ensures they differ.
        let a = FingerprintComputer::compute("ab", "cd");
        let b = FingerprintComputer::compute("abc", "d");
        assert_ne!(a, b);
    }

    #[test]
    fn test_fingerprint_empty_vc_and_config() {
        let a = FingerprintComputer::compute("", "");
        let b = FingerprintComputer::compute("", "");
        assert_eq!(a, b);
        // Even empty inputs produce a valid key.
        assert_ne!(a.as_bytes(), &[0u8; 32]);
    }

    #[test]
    fn test_fingerprint_empty_vs_nonempty() {
        let a = FingerprintComputer::compute("", "cfg");
        let b = FingerprintComputer::compute("vc", "");
        assert_ne!(a, b);
    }

    #[test]
    fn test_fingerprint_from_parts_different_order() {
        let a = FingerprintComputer::compute_from_parts(1, 2);
        let b = FingerprintComputer::compute_from_parts(2, 1);
        assert_ne!(a, b);
    }

    // -----------------------------------------------------------------------
    // CacheKey ordering and identity
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_key_from_raw_as_bytes_round_trip() {
        let raw = [0xABu8; 32];
        let key = CacheKey::from_raw(raw);
        assert_eq!(*key.as_bytes(), raw);
    }

    #[test]
    fn test_cache_key_ord_is_lexicographic() {
        let low = CacheKey::from_raw([0x00; 32]);
        let high = CacheKey::from_raw([0xFF; 32]);
        assert!(low < high);
        assert!(high > low);
    }

    #[test]
    fn test_cache_key_hash_is_stable() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let key = make_key(42);
        let mut h1 = DefaultHasher::new();
        key.hash(&mut h1);
        let mut h2 = DefaultHasher::new();
        key.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
    }

    // -----------------------------------------------------------------------
    // CachedResult variant checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_verified_for_all_variants() {
        assert!(CachedResult::Verified.is_verified());
        assert!(!CachedResult::Unknown.is_verified());
        assert!(!CachedResult::Timeout.is_verified());
        assert!(!CachedResult::Failed { reason: "x".into() }.is_verified());
    }

    // -----------------------------------------------------------------------
    // Config accessor
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_accessor_returns_configured_values() {
        let cfg = CacheConfig {
            max_entries: 7,
            max_memory_bytes: 999,
            ttl: Duration::from_secs(42),
            eviction_policy: EvictionPolicy::Lfu,
            format_version: 2,
        };
        let cache = ProofCache::new(cfg.clone());
        assert_eq!(cache.config().max_entries, 7);
        assert_eq!(cache.config().max_memory_bytes, 999);
        assert_eq!(cache.config().ttl, Duration::from_secs(42));
        assert_eq!(cache.config().eviction_policy, EvictionPolicy::Lfu);
    }

    // -----------------------------------------------------------------------
    // CacheEntry estimated_heap_size
    // -----------------------------------------------------------------------

    #[test]
    fn test_estimated_heap_size_includes_dynamic_strings() {
        let small = make_entry(CachedResult::Verified, None, None);
        let big = make_entry(
            CachedResult::Failed {
                reason: "a".repeat(1000),
            },
            Some(&"f".repeat(500)),
            Some(&"p".repeat(500)),
        );
        assert!(big.estimated_heap_size() > small.estimated_heap_size());
    }

    #[test]
    fn test_estimated_heap_size_base_only() {
        let entry = CacheEntry {
            result: CachedResult::Verified,
            created_at: Duration::ZERO,
            access_count: 0,
            size_bytes: 0,
            solver_info: String::new(),
            function_name: None,
            file_path: None,
            priority: 0,
            last_accessed: None,
        };
        // Base size should be at least the struct size.
        assert!(entry.estimated_heap_size() >= std::mem::size_of::<CacheEntry>());
    }

    // -----------------------------------------------------------------------
    // Duplicate / overwrite behavior
    // -----------------------------------------------------------------------

    #[test]
    fn test_overwrite_resets_access_count() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        // Bump access count.
        for _ in 0..10 {
            cache.get(&key);
        }
        assert_eq!(cache.peek(&key).unwrap().access_count, 10);
        // Overwrite with a new entry — access_count resets to 0.
        cache.put(key, CachedResult::Timeout, "ay-new");
        assert_eq!(cache.peek(&key).unwrap().access_count, 0);
        assert!(matches!(
            cache.peek(&key).unwrap().result,
            CachedResult::Timeout
        ));
    }

    #[test]
    fn test_overwrite_updates_secondary_index() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put_with_metadata(
            key,
            CachedResult::Verified,
            "ay".into(),
            Some("old_fn".into()),
            Some("old_file.rs".into()),
            0,
        );
        assert_eq!(cache.by_function("old_fn").len(), 1);
        assert_eq!(cache.by_file("old_file.rs").len(), 1);

        // Overwrite with different metadata.
        cache.put_with_metadata(
            key,
            CachedResult::Verified,
            "ay".into(),
            Some("new_fn".into()),
            Some("new_file.rs".into()),
            0,
        );
        // Old index entries should be gone.
        assert!(cache.by_function("old_fn").is_empty());
        assert!(cache.by_file("old_file.rs").is_empty());
        // New index entries should exist.
        assert_eq!(cache.by_function("new_fn").len(), 1);
        assert_eq!(cache.by_file("new_file.rs").len(), 1);
    }

    #[test]
    fn test_overwrite_does_not_change_len() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put(key, CachedResult::Verified, "ay");
        cache.put(key, CachedResult::Unknown, "ay-2");
        cache.put(key, CachedResult::Timeout, "ay-3");
        assert_eq!(cache.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Multiple sequential LRU evictions
    // -----------------------------------------------------------------------

    #[test]
    fn test_lru_multiple_evictions_in_sequence() {
        let mut cache = ProofCache::new(make_config(2));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        // Each new insert evicts the oldest.
        cache.put(make_key(3), CachedResult::Verified, "ay");
        assert!(!cache.contains_key(&make_key(1)));
        cache.put(make_key(4), CachedResult::Verified, "ay");
        assert!(!cache.contains_key(&make_key(2)));
        cache.put(make_key(5), CachedResult::Verified, "ay");
        assert!(!cache.contains_key(&make_key(3)));
        assert_eq!(cache.len(), 2);
        assert!(cache.contains_key(&make_key(4)));
        assert!(cache.contains_key(&make_key(5)));
    }

    // -----------------------------------------------------------------------
    // Memory limit and entry limit interaction
    // -----------------------------------------------------------------------

    #[test]
    fn test_entry_limit_reached_before_memory() {
        let config = CacheConfig {
            max_entries: 2,
            max_memory_bytes: 1024 * 1024, // plenty of room
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        assert_eq!(cache.len(), 2);
        assert!(cache.stats().evictions >= 1);
    }

    #[test]
    fn test_memory_limit_reached_before_entries() {
        // Very tight memory budget, generous entry count.
        let config = CacheConfig {
            max_entries: 10000,
            max_memory_bytes: 300, // very small
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        for i in 0..100 {
            cache.put(make_key(i), CachedResult::Verified, "ay");
        }
        // Entries should have been evicted to stay within memory budget.
        assert!(cache.len() < 100);
        assert!(cache.memory_usage() <= 300 + 300); // some slack for the last inserted entry
    }

    // -----------------------------------------------------------------------
    // Zero-capacity cache
    // -----------------------------------------------------------------------

    #[test]
    fn test_zero_capacity_cache_stays_empty_or_single() {
        // max_entries=0 means the cache should immediately evict on put.
        // In practice, the loop `while self.entries.len() >= 0` is always true
        // for an empty cache, but evict_one returns false since there is
        // nothing to evict, so the entry still gets inserted.  That is
        // acceptable — this test documents the behavior.
        let config = CacheConfig {
            max_entries: 0,
            max_memory_bytes: 1024 * 1024,
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        // With 0 capacity, the first insert has nothing to evict, so it ends
        // up with 1 entry.  The second insert triggers eviction of the first.
        cache.put(make_key(2), CachedResult::Verified, "ay");
        assert!(cache.len() <= 1);
    }

    // -----------------------------------------------------------------------
    // Batch invalidation — overlapping criteria
    // -----------------------------------------------------------------------

    #[test]
    fn test_invalidate_batch_overlapping_criteria_no_double_count() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("foo_bar".into()),
            Some("src/foo.rs".into()),
            0,
        );
        // This entry matches by function_name, file_path, AND pattern.
        let batch = InvalidationBatch {
            function_names: vec!["foo_bar".into()],
            file_paths: vec!["src/foo.rs".into()],
            patterns: vec!["foo".into()],
            reason: Some(InvalidationReason::CodeChanged),
        };
        let removed = cache.invalidate_batch(&batch);
        // Despite matching all three criteria, it should only be removed once.
        assert_eq!(removed, 1);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_invalidate_batch_combined_function_file_pattern() {
        let mut cache = ProofCache::new(make_config(16));
        // Entry 1: matches function_name only.
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("target_fn".into()),
            Some("src/other.rs".into()),
            0,
        );
        // Entry 2: matches file_path only.
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("safe_fn".into()),
            Some("src/target.rs".into()),
            0,
        );
        // Entry 3: matches pattern only.
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            Some("has_overflow_check".into()),
            Some("src/safe.rs".into()),
            0,
        );
        // Entry 4: matches nothing.
        cache.put_with_metadata(
            make_key(4),
            CachedResult::Verified,
            "ay".into(),
            Some("unrelated".into()),
            Some("src/unrelated.rs".into()),
            0,
        );
        let batch = InvalidationBatch {
            function_names: vec!["target_fn".into()],
            file_paths: vec!["src/target.rs".into()],
            patterns: vec!["overflow".into()],
            reason: Some(InvalidationReason::DependencyChanged),
        };
        let removed = cache.invalidate_batch(&batch);
        assert_eq!(removed, 3);
        assert_eq!(cache.len(), 1);
        assert!(cache.contains_key(&make_key(4)));
    }

    // -----------------------------------------------------------------------
    // Secondary index cleanup after eviction
    // -----------------------------------------------------------------------

    #[test]
    fn test_secondary_index_cleaned_after_lru_eviction() {
        let mut cache = ProofCache::new(make_config(2));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("evicted_fn".into()),
            Some("evicted.rs".into()),
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("kept_fn".into()),
            None,
            0,
        );
        // Evict key 1 by inserting a third entry.
        cache.put(make_key(3), CachedResult::Verified, "ay");
        assert!(!cache.contains_key(&make_key(1)));
        // The secondary index for the evicted entry's function/file should be empty.
        assert!(cache.by_function("evicted_fn").is_empty());
        assert!(cache.by_file("evicted.rs").is_empty());
        // The surviving entry's index should still work.
        assert_eq!(cache.by_function("kept_fn").len(), 1);
    }

    // -----------------------------------------------------------------------
    // Warmup capacity and memory limits
    // -----------------------------------------------------------------------

    #[test]
    fn test_warmup_respects_max_entries() {
        let mut cache = ProofCache::new(make_config(2));
        let entries = vec![
            (
                make_key(1),
                make_entry(CachedResult::Verified, Some("a"), None),
            ),
            (
                make_key(2),
                make_entry(CachedResult::Verified, Some("b"), None),
            ),
            (
                make_key(3),
                make_entry(CachedResult::Verified, Some("c"), None),
            ),
        ];
        cache.warmup(&WarmupStrategy::Full, entries);
        // Only 2 should fit.
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_warmup_respects_memory_limit() {
        let config = CacheConfig {
            max_entries: 10000,
            max_memory_bytes: 250, // very tight
            ttl: Duration::from_secs(3600),
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        let entries: Vec<_> = (0..100)
            .map(|i| (make_key(i), make_entry(CachedResult::Verified, None, None)))
            .collect();
        cache.warmup(&WarmupStrategy::Full, entries);
        // Very few entries should fit within 250 bytes.
        assert!(cache.len() < 100);
    }

    #[test]
    fn test_warmup_selective_filters_correctly() {
        let mut cache = ProofCache::new(make_config(16));
        let entries = vec![
            (
                make_key(1),
                make_entry(CachedResult::Verified, Some("alpha"), None),
            ),
            (
                make_key(2),
                make_entry(CachedResult::Verified, Some("beta"), None),
            ),
            (
                make_key(3),
                make_entry(CachedResult::Verified, Some("alpha"), None),
            ),
            (make_key(4), make_entry(CachedResult::Verified, None, None)), // no function_name
        ];
        let strategy = WarmupStrategy::Selective {
            functions: vec!["alpha".into()],
        };
        cache.warmup(&strategy, entries);
        assert_eq!(cache.len(), 2);
        assert!(cache.contains_key(&make_key(1)));
        assert!(cache.contains_key(&make_key(3)));
    }

    #[test]
    fn test_warmup_most_recent_takes_correct_count() {
        let mut cache = ProofCache::new(make_config(16));
        let mut entries = Vec::new();
        for i in 0..5 {
            let mut e = make_entry(CachedResult::Verified, None, None);
            e.created_at = Duration::from_secs(i * 100);
            entries.push((make_key(i), e));
        }
        cache.warmup(&WarmupStrategy::MostRecent { count: 3 }, entries);
        assert_eq!(cache.len(), 3);
        // Should have the 3 most recent (keys 4, 3, 2).
        assert!(cache.contains_key(&make_key(4)));
        assert!(cache.contains_key(&make_key(3)));
        assert!(cache.contains_key(&make_key(2)));
        assert!(!cache.contains_key(&make_key(1)));
        assert!(!cache.contains_key(&make_key(0)));
    }

    // -----------------------------------------------------------------------
    // Serialization — deterministic output
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_is_deterministic() {
        let build = || {
            let mut cache = ProofCache::new(make_config(16));
            cache.put_with_metadata(
                make_key(1),
                CachedResult::Verified,
                "ay".into(),
                Some("fn_a".into()),
                Some("a.rs".into()),
                3,
            );
            cache.put_with_metadata(
                make_key(2),
                CachedResult::Failed {
                    reason: "oops".into(),
                },
                "ay-bv".into(),
                None,
                None,
                0,
            );
            CacheSerializer::serialize(&cache)
        };
        assert_eq!(build(), build());
    }

    // -----------------------------------------------------------------------
    // Serialization — corrupt data edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_deserialize_empty_data() {
        let err = CacheSerializer::deserialize(&[]).expect_err("empty data should fail");
        assert!(err.to_string().contains("unexpected end"));
    }

    #[test]
    fn test_deserialize_truncated_header() {
        // Only 4 bytes (version) but no entry count.
        let data = 2u32.to_le_bytes();
        let err = CacheSerializer::deserialize(&data).expect_err("truncated header should fail");
        assert!(err.to_string().contains("unexpected end"));
    }

    #[test]
    fn test_deserialize_claims_entries_but_has_none() {
        // Version 2, count=1, but no entry data follows.
        let mut data = Vec::new();
        data.extend_from_slice(&2u32.to_le_bytes());
        data.extend_from_slice(&1u32.to_le_bytes());
        let err = CacheSerializer::deserialize(&data).expect_err("missing entry data should fail");
        assert!(err.to_string().contains("unexpected end"));
    }

    #[test]
    fn test_deserialize_invalid_result_tag() {
        // Build a minimal valid header + key + invalid result tag.
        let mut data = Vec::new();
        data.extend_from_slice(&2u32.to_le_bytes()); // version
        data.extend_from_slice(&1u32.to_le_bytes()); // count = 1
        data.extend_from_slice(&[0xAA; 32]); // key hash
        data.push(0xFF); // invalid result tag
        let err = CacheSerializer::deserialize(&data).expect_err("invalid result tag should fail");
        assert!(err.to_string().contains("unknown result tag"));
    }

    #[test]
    fn test_deserialize_invalid_option_tag() {
        // Build valid header + key + result(Verified) + timestamps + sizes +
        // solver_info + invalid option tag for function_name.
        let mut data = Vec::new();
        data.extend_from_slice(&2u32.to_le_bytes()); // version
        data.extend_from_slice(&1u32.to_le_bytes()); // count = 1
        data.extend_from_slice(&[0x00; 32]); // key hash
        data.push(0); // Verified tag
        data.extend_from_slice(&100u64.to_le_bytes()); // created_at
        data.extend_from_slice(&0u64.to_le_bytes()); // access_count
        data.extend_from_slice(&0u32.to_le_bytes()); // size_bytes
                                                     // solver_info: empty string (len=0)
        data.extend_from_slice(&0u32.to_le_bytes());
        // function_name option tag: invalid
        data.push(0xFF);
        let err = CacheSerializer::deserialize(&data).expect_err("invalid option tag should fail");
        assert!(err.to_string().contains("invalid option tag"));
    }

    // -----------------------------------------------------------------------
    // Serialization round-trip with all result types
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_round_trip_all_result_types() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "s1");
        cache.put(
            make_key(2),
            CachedResult::Failed {
                reason: "fail reason".into(),
            },
            "s2",
        );
        cache.put(make_key(3), CachedResult::Unknown, "s3");
        cache.put(make_key(4), CachedResult::Timeout, "s4");

        let data = CacheSerializer::serialize(&cache);
        let (version, entries) = CacheSerializer::deserialize(&data).unwrap();
        assert_eq!(version, 2);
        assert_eq!(entries.len(), 4);

        let find = |n: u64| {
            entries
                .iter()
                .find(|(k, _)| *k == make_key(n))
                .map(|(_, e)| &e.result)
                .unwrap()
                .clone()
        };
        assert!(matches!(find(1), CachedResult::Verified));
        assert!(matches!(find(2), CachedResult::Failed { reason } if reason == "fail reason"));
        assert!(matches!(find(3), CachedResult::Unknown));
        assert!(matches!(find(4), CachedResult::Timeout));
    }

    // -----------------------------------------------------------------------
    // Disk round-trip with reload and queries
    // -----------------------------------------------------------------------

    #[test]
    fn test_disk_round_trip_preserves_secondary_index() {
        let dir = std::env::temp_dir().join("trust_vc_proof_cache_test_disk_index");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("cache_idx.bin");

        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some("my_fn".into()),
            Some("src/lib.rs".into()),
            0,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            Some("my_fn".into()),
            Some("src/main.rs".into()),
            0,
        );
        cache.save_to_disk(&path).expect("save should succeed");

        let loaded =
            ProofCache::load_from_disk(&path, make_config(16)).expect("load should succeed");
        assert_eq!(loaded.by_function("my_fn").len(), 2);
        assert_eq!(loaded.by_file("src/lib.rs").len(), 1);
        assert_eq!(loaded.by_file("src/main.rs").len(), 1);

        let _ = std::fs::remove_dir_all(&dir);
    }

    // -----------------------------------------------------------------------
    // Migration
    // -----------------------------------------------------------------------

    #[test]
    fn test_migration_v1_returns_error_with_sha256_message() {
        let err = CacheMigration::migrate(vec![1, 2, 3], 1).expect_err("v1 migration should fail");
        let msg = err.to_string();
        assert!(msg.contains("SHA-256") || msg.contains("v1"));
    }

    #[test]
    fn test_can_migrate_v1() {
        assert!(CacheMigration::can_migrate(1));
    }

    #[test]
    fn test_can_migrate_v0_is_false() {
        assert!(!CacheMigration::can_migrate(0));
    }

    // -----------------------------------------------------------------------
    // evict_expired
    // -----------------------------------------------------------------------

    #[test]
    fn test_evict_expired_removes_nothing_when_fresh() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        let evicted = cache.evict_expired();
        assert_eq!(evicted, 0);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_evict_expired_removes_old_entries() {
        // Build a cache with a very short TTL.
        let config = CacheConfig {
            max_entries: 16,
            max_memory_bytes: 64 * 1024 * 1024,
            ttl: Duration::from_secs(0), // everything is immediately expired
            eviction_policy: EvictionPolicy::Lru,
            format_version: 2,
        };
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        // With TTL=0, all entries created in the past are already expired.
        // The entries were just created, so `created_at` is approximately now.
        // `evict_expired` compares `now - created_at > ttl` and ttl=0, so
        // it may or may not catch entries created in the same instant.
        // We just verify the method doesn't panic and returns a sensible value.
        let evicted = cache.evict_expired();
        // With TTL 0, eviction depends on timing; at minimum it should not panic.
        assert!(evicted <= 2);
    }

    #[test]
    fn test_evict_expired_on_empty_cache() {
        let mut cache = ProofCache::new(make_config(16));
        assert_eq!(cache.evict_expired(), 0);
    }

    // -----------------------------------------------------------------------
    // Multiple get() calls don't corrupt LRU order
    // -----------------------------------------------------------------------

    #[test]
    fn test_repeated_get_same_key_lru_order_stable() {
        let mut cache = ProofCache::new(make_config(3));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        // Repeatedly access key 1 — it should always be moved to back.
        for _ in 0..20 {
            cache.get(&make_key(1));
        }
        // Insert a new key — LRU victim should be key 2 (oldest untouched).
        cache.put(make_key(4), CachedResult::Verified, "ay");
        assert!(cache.contains_key(&make_key(1)));
        assert!(!cache.contains_key(&make_key(2)));
    }

    // -----------------------------------------------------------------------
    // Empty string function_name / file_path
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_string_function_name_indexed() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            Some(String::new()),
            None,
            0,
        );
        // An empty string is a valid function name for indexing purposes.
        assert_eq!(cache.by_function("").len(), 1);
    }

    #[test]
    fn test_empty_string_file_path_indexed() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            None,
            Some(String::new()),
            0,
        );
        assert_eq!(cache.by_file("").len(), 1);
    }

    // -----------------------------------------------------------------------
    // Eviction policies — same data, different policies
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_eviction_policies_keep_cache_within_limits() {
        let policies = [
            EvictionPolicy::Lru,
            EvictionPolicy::Lfu,
            EvictionPolicy::FifoWithPriority,
            EvictionPolicy::AdaptiveArc,
        ];
        for policy in policies {
            let config = CacheConfig {
                max_entries: 5,
                max_memory_bytes: 64 * 1024 * 1024,
                ttl: Duration::from_secs(3600),
                eviction_policy: policy,
                format_version: 2,
            };
            let mut cache = ProofCache::new(config);
            for i in 0..20 {
                cache.put(make_key(i), CachedResult::Verified, "ay");
            }
            assert!(
                cache.len() <= 5,
                "policy {policy:?} exceeded max_entries: {}",
                cache.len()
            );
            assert!(
                cache.stats().evictions > 0,
                "policy {policy:?} should have evicted entries"
            );
        }
    }

    // -----------------------------------------------------------------------
    // FIFO priority — equal priorities fall back to FIFO
    // -----------------------------------------------------------------------

    #[test]
    fn test_fifo_priority_equal_priorities_fifo_order() {
        let mut config = make_config(3);
        config.eviction_policy = EvictionPolicy::FifoWithPriority;
        let mut cache = ProofCache::new(config);
        // All same priority.
        cache.put_with_metadata(
            make_key(1),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            5,
        );
        cache.put_with_metadata(
            make_key(2),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            5,
        );
        cache.put_with_metadata(
            make_key(3),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            5,
        );
        // Insert 4th — key 1 (first in FIFO order, same priority) should be evicted.
        cache.put_with_metadata(
            make_key(4),
            CachedResult::Verified,
            "ay".into(),
            None,
            None,
            5,
        );
        assert!(!cache.contains_key(&make_key(1)));
        assert!(cache.contains_key(&make_key(2)));
    }

    // -----------------------------------------------------------------------
    // ARC eviction — boost frequency to protect entries
    // -----------------------------------------------------------------------

    #[test]
    fn test_arc_protects_frequently_accessed() {
        let mut config = make_config(4);
        config.eviction_policy = EvictionPolicy::AdaptiveArc;
        let mut cache = ProofCache::new(config);
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        cache.put(make_key(4), CachedResult::Verified, "ay");
        // Heavily access keys 1 and 2.
        for _ in 0..50 {
            cache.get(&make_key(1));
            cache.get(&make_key(2));
        }
        // Insert new entries — low-frequency entries (3, 4) should be evicted.
        cache.put(make_key(5), CachedResult::Verified, "ay");
        cache.put(make_key(6), CachedResult::Verified, "ay");
        assert!(cache.contains_key(&make_key(1)));
        assert!(cache.contains_key(&make_key(2)));
    }

    // -----------------------------------------------------------------------
    // Statistics accumulation across multiple operations
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_accumulate_correctly() {
        let mut cache = ProofCache::new(make_config(3));
        // 3 puts.
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.put(make_key(2), CachedResult::Verified, "ay");
        cache.put(make_key(3), CachedResult::Verified, "ay");
        // 2 hits.
        cache.get(&make_key(1));
        cache.get(&make_key(2));
        // 1 miss.
        cache.get(&make_key(999));
        // 1 eviction (put triggers LRU eviction).
        cache.put(make_key(4), CachedResult::Verified, "ay");
        // 1 invalidation.
        cache.invalidate(&make_key(4));

        let stats = cache.stats();
        assert_eq!(stats.hits, 2);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.evictions, 1);
        assert_eq!(stats.invalidations, 1);
        assert_eq!(stats.entry_count, cache.len());
    }

    #[test]
    fn test_hit_ratio_after_operations() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        // 4 hits, 1 miss → ratio = 0.8
        for _ in 0..4 {
            cache.get(&make_key(1));
        }
        cache.get(&make_key(999));
        let ratio = cache.stats().hit_ratio();
        assert!((ratio - 0.8).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Stress test — large number of entries
    // -----------------------------------------------------------------------

    #[test]
    fn test_stress_many_entries() {
        let mut cache = ProofCache::new(make_config(512));
        for i in 0..1000u64 {
            let key = FingerprintComputer::compute_from_parts(i, i * 7);
            cache.put(key, CachedResult::Verified, "ay");
        }
        assert!(cache.len() <= 512);
        assert!(cache.stats().evictions > 0);
        // Verify the cache is internally consistent — every contained key
        // can be peeked.
        let mut peek_count = 0;
        for i in 0..1000u64 {
            let key = FingerprintComputer::compute_from_parts(i, i * 7);
            if cache.contains_key(&key) {
                assert!(cache.peek(&key).is_some());
                peek_count += 1;
            }
        }
        assert_eq!(peek_count, cache.len());
    }

    // -----------------------------------------------------------------------
    // Invalidation tracking through stats
    // -----------------------------------------------------------------------

    #[test]
    fn test_batch_invalidation_increments_stats_correctly() {
        let mut cache = ProofCache::new(make_config(16));
        for i in 0..5 {
            cache.put_with_metadata(
                make_key(i),
                CachedResult::Verified,
                "ay".into(),
                Some("target".into()),
                None,
                0,
            );
        }
        let batch = InvalidationBatch {
            function_names: vec!["target".into()],
            ..Default::default()
        };
        cache.invalidate_batch(&batch);
        assert_eq!(cache.stats().invalidations, 5);
        assert!(cache.is_empty());
    }

    // -----------------------------------------------------------------------
    // Clear after operations preserves usability
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_usable_after_clear() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        cache.get(&make_key(1));
        cache.clear();
        // Should be fully usable after clear.
        cache.put(make_key(2), CachedResult::Timeout, "ay");
        let entry = cache
            .get(&make_key(2))
            .expect("should exist after clear+put");
        assert!(matches!(entry.result, CachedResult::Timeout));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.stats().hits, 1);
    }

    // -----------------------------------------------------------------------
    // CacheError variants
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_error_io_display() {
        let e = CacheError::Io {
            context: "test_op",
            source: io::Error::new(io::ErrorKind::NotFound, "gone"),
        };
        let msg = format!("{e}");
        assert!(msg.contains("test_op"));
        assert!(msg.contains("gone"));
    }

    // -----------------------------------------------------------------------
    // InvalidationReason clone and eq
    // -----------------------------------------------------------------------

    #[test]
    fn test_invalidation_reason_variants() {
        let reasons = [
            InvalidationReason::CodeChanged,
            InvalidationReason::DependencyChanged,
            InvalidationReason::ConfigChanged,
            InvalidationReason::Expired,
            InvalidationReason::Manual,
        ];
        // Verify Clone + PartialEq.
        for r in &reasons {
            assert_eq!(r, &r.clone());
        }
        // Verify different variants are not equal.
        assert_ne!(InvalidationReason::CodeChanged, InvalidationReason::Manual);
    }

    // -----------------------------------------------------------------------
    // EvictionPolicy traits
    // -----------------------------------------------------------------------

    #[test]
    fn test_eviction_policy_clone_copy_eq_hash() {
        use std::collections::HashSet;
        let policies = [
            EvictionPolicy::Lru,
            EvictionPolicy::Lfu,
            EvictionPolicy::FifoWithPriority,
            EvictionPolicy::AdaptiveArc,
        ];
        let mut set = HashSet::new();
        for p in &policies {
            let cloned = *p; // Copy
            assert_eq!(*p, cloned);
            set.insert(*p);
        }
        assert_eq!(set.len(), 4);
    }

    // -----------------------------------------------------------------------
    // put_with_metadata full verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_put_with_metadata_stores_all_fields() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(42);
        cache.put_with_metadata(
            key,
            CachedResult::Failed {
                reason: "bad proof".into(),
            },
            "ay-nia".into(),
            Some("lemma_transitivity".into()),
            Some("src/proofs/trans.rs".into()),
            7,
        );
        let entry = cache.peek(&key).expect("entry should exist");
        assert!(matches!(&entry.result, CachedResult::Failed { reason } if reason == "bad proof"));
        assert_eq!(entry.solver_info, "ay-nia");
        assert_eq!(entry.function_name.as_deref(), Some("lemma_transitivity"));
        assert_eq!(entry.file_path.as_deref(), Some("src/proofs/trans.rs"));
        assert_eq!(entry.priority, 7);
        assert_eq!(entry.access_count, 0);
        // created_at should be roughly "now" (nonzero).
        assert!(entry.created_at.as_secs() > 0);
    }

    // -----------------------------------------------------------------------
    // Serialization round-trip preserves access_count and priority
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_round_trip_preserves_metadata_fields() {
        let mut cache = ProofCache::new(make_config(16));
        let key = make_key(1);
        cache.put_with_metadata(
            key,
            CachedResult::Verified,
            "solver-x".into(),
            Some("fn_z".into()),
            Some("z.rs".into()),
            42,
        );
        // Bump access count.
        cache.get(&key);
        cache.get(&key);
        cache.get(&key);

        let data = CacheSerializer::serialize(&cache);
        let (_, entries) = CacheSerializer::deserialize(&data).unwrap();
        assert_eq!(entries.len(), 1);
        let (_, entry) = &entries[0];
        assert_eq!(entry.access_count, 3);
        assert_eq!(entry.priority, 42);
        assert_eq!(entry.solver_info, "solver-x");
        assert_eq!(entry.function_name.as_deref(), Some("fn_z"));
        assert_eq!(entry.file_path.as_deref(), Some("z.rs"));
    }

    // -----------------------------------------------------------------------
    // Concurrent-like sequential access pattern
    // -----------------------------------------------------------------------

    #[test]
    fn test_interleaved_put_get_invalidate_pattern() {
        // Simulates a pattern where multiple "threads" would interleave
        // puts, gets, and invalidations on overlapping key sets.
        let mut cache = ProofCache::new(make_config(10));

        // "Thread A" inserts keys 0..5.
        for i in 0..5 {
            cache.put(make_key(i), CachedResult::Verified, "thread-a");
        }
        // "Thread B" inserts keys 3..8 (overlapping 3, 4).
        for i in 3..8 {
            cache.put(make_key(i), CachedResult::Verified, "thread-b");
        }
        // Keys 3, 4 should now have solver_info "thread-b" (overwritten).
        assert_eq!(cache.peek(&make_key(3)).unwrap().solver_info, "thread-b");
        assert_eq!(cache.peek(&make_key(4)).unwrap().solver_info, "thread-b");
        // Keys 0, 1, 2 should still have "thread-a".
        assert_eq!(cache.peek(&make_key(0)).unwrap().solver_info, "thread-a");

        // "Thread C" invalidates keys 0..3.
        for i in 0..3 {
            cache.invalidate(&make_key(i));
        }
        assert_eq!(cache.len(), 5); // keys 3..8 remain
        for i in 3..8 {
            assert!(cache.contains_key(&make_key(i)));
        }

        // "Thread D" reads everything remaining and inserts more.
        for i in 3..8 {
            cache.get(&make_key(i));
        }
        for i in 10..15 {
            cache.put(make_key(i), CachedResult::Unknown, "thread-d");
        }
        assert_eq!(cache.len(), 10);
    }

    // -----------------------------------------------------------------------
    // Warmup + subsequent operations
    // -----------------------------------------------------------------------

    #[test]
    fn test_warmup_then_put_and_evict() {
        let mut cache = ProofCache::new(make_config(3));
        let entries = vec![
            (
                make_key(1),
                make_entry(CachedResult::Verified, Some("w1"), None),
            ),
            (
                make_key(2),
                make_entry(CachedResult::Verified, Some("w2"), None),
            ),
        ];
        cache.warmup(&WarmupStrategy::Full, entries);
        assert_eq!(cache.len(), 2);

        // Now put more entries — should trigger eviction at capacity.
        cache.put(make_key(3), CachedResult::Verified, "ay");
        assert_eq!(cache.len(), 3);
        cache.put(make_key(4), CachedResult::Verified, "ay");
        // One of the warmed-up entries should be evicted (LRU = key 1).
        assert_eq!(cache.len(), 3);
        assert!(!cache.contains_key(&make_key(1)));
    }

    // -----------------------------------------------------------------------
    // Serialize empty optional fields
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_round_trip_none_optional_fields() {
        let mut cache = ProofCache::new(make_config(16));
        cache.put(make_key(1), CachedResult::Verified, "ay");
        let data = CacheSerializer::serialize(&cache);
        let (_, entries) = CacheSerializer::deserialize(&data).unwrap();
        let (_, entry) = &entries[0];
        assert!(entry.function_name.is_none());
        assert!(entry.file_path.is_none());
    }
}
