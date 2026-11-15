//! Identities used across VcIR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Items are identified by content hashes of their definition paths, never
//! by name: two functions called `requires` in different modules, or a user
//! function shadowing a marker, are different items. Locals, sites and spans
//! are small indices local to one function or one producer.

/// A 128-bit stable hash of a definition path (rustc's `DefPathHash`): the
/// identity of an item across compilations and crates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefHash {
    /// High 64 bits.
    pub hi: u64,
    /// Low 64 bits.
    pub lo: u64,
}

impl DefHash {
    /// A hash from its two halves.
    #[must_use]
    pub const fn new(hi: u64, lo: u64) -> Self {
        Self { hi, lo }
    }
}

/// Identity of a function (free function, method, trait method).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnId(pub DefHash);

/// Identity of a struct or enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AdtId(pub DefHash);

/// Index of a local in its function's [`crate::FnDecl::locals`] table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

impl LocalId {
    /// The table index.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// A checked site of a function: an assertion, a call's precondition, a
/// return's postcondition, or an exec operation that can panic. Unique within
/// its function; a verdict is reported per site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SiteId(pub u32);

/// A loop of a function. Unique within its function; `break` and `continue`
/// name the loop they leave or restart by it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LoopId(pub u32);

/// A source position chosen by the producer. VcIR never interprets it; the
/// producer maps it back to its own span type when it reports a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SpanId(pub u32);
