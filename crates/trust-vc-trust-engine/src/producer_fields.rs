// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! THE DERIVED ENUMERATION of every producer field that crosses into this crate.
//!
//! # Why this file exists, and why it is not prose
//!
//! Adversarial review round 7 wrote an enumeration of "every point where a
//! producer claim can influence a verdict" (P1-P7, E1-E24, at
//! [`crate::native_discharge`]). Round 8 found it had missed AN ENTIRE SEAM —
//! the assertion id this crate PUBLISHES — and named the method failure exactly:
//! the enumeration was HAND-WRITTEN, and its own "how to check this list is
//! complete" recipe grepped `native_discharge/*.rs` for six receiver names. The
//! export seam lives in `native_trust_ir_bundle.rs` and reads
//! `compiler_facts.obligation_sources[]`, so no recipe scoped that way could
//! ever have found it.
//!
//! Round 9 then found the SAME method failure one level up: the replacement was
//! field-derived but TYPE-scoped by hand. Sixteen type names a person typed were
//! pinned, and the read-site scan iterated over the fields ALREADY IN THE TABLE,
//! so a field of an un-tabled type could gain read sites freely. A mechanical
//! scan of this crate's sources named 59 `trust_ir` types, 43 of them outside
//! the sixteen — including `Inst` (the whole program semantics), `ProofEvidence`
//! (whose `CleanCic { term, lineage, .. }` IS the kernel-recheck guard) and
//! `NativeVerificationBundleError` (one variant of which this lane destructures
//! to carry an upstream refusal PAST).
//!
//! This table is DERIVED, and so is the set of types it covers:
//!
//! 1. the FIELD LIST comes from the producer types themselves —
//!    [`producer_types_are_exhaustively_enumerated`] and
//!    `producer_value_types_are_exhaustively_enumerated` destructure each one
//!    exhaustively (enums variant by variant, and every field of every variant),
//!    so a field or variant added or removed upstream fails to COMPILE;
//! 2. the TYPE CLOSURE comes from the crate's own sources —
//!    `every_trust_ir_type_this_crate_names_is_tabled_or_excluded` derives every
//!    `trust_ir` type this crate NAMES and requires each one to be tabled or
//!    listed in [`UNTABLED_PRODUCER_TYPES`] with a reason;
//! 3. the READ SITES come from scanning this crate's own sources —
//!    `producer_field_read_sites_match_the_table` re-derives them at test time
//!    and fails when a field or variant gains (or loses) a file, so the table
//!    cannot drift away from the code the way the prose list did;
//! 4. STRUCT PATTERNS, which read fields without writing `.field`, are covered
//!    by `producer_struct_brace_sites_match_the_table`
//!    ([`PRODUCER_TYPE_BRACE_SITES`]).
//!
//! The scan covers the WHOLE crate (`src/**/*.rs`), not one directory.
//!
//! # What "read site" means here, exactly
//!
//! A file appears in a row's `read_sites` iff its CODE contains the token
//! `.<field>` (field-access syntax). Comments and string literals are blanked
//! out first (`strip_comments_and_strings`), so a doc comment that WRITES a
//! field path — this module is full of them — is not a read site. That is a
//! deliberately MECHANICAL definition, and it has two known imprecisions, both
//! stated rather than smoothed over:
//!
//! * IT CANNOT ATTRIBUTE BY TYPE. `read_sites` is therefore the union over every
//!   producer type that shares the field NAME, and rows with the same `field`
//!   carry the same set. `.id`, `.name`, `.kind`, `.status`, `.mode`, `.source`,
//!   `.span` and `.obligations` also name fields of trust-vc's OWN types, so a
//!   row may list a file that never touches the producer type; where that is so,
//!   the `note` says which other field the site actually is. A false positive
//!   makes the ratchet LESS sensitive in that file, never more permissive about
//!   anything else.
//! * IT IS THE RULE FOR STRUCT FIELDS ONLY. A row for an enum VARIANT
//!   ([`ProducerFieldKind::NamedPath`]) is scanned by the full path
//!   `Type::Variant`, so its attribution is exact.
//!
//! CORRECTED, round 9. This section used to claim a third imprecision and then
//! dismiss it: "An exhaustive destructuring reads a field without writing
//! `.field`. MEASURED at the time of writing: this crate contains no
//! destructuring pattern for any producer type." That was FALSE — the crate
//! holds about forty `Type::Variant { field, .. }` patterns, and one
//! (`Inst::Call { callee, .. }`, `native_discharge/body.rs`) was added by the
//! very commit that wrote the sentence. It was also load-bearing: the shape the
//! scan admitted it could not see was the shape it was full of. `.callee` does
//! not appear anywhere in this crate; `Inst::Call` does.
//!
//! Both halves are now scanned: enum payloads through the variant PATH, and
//! producer STRUCT braces through [`PRODUCER_TYPE_BRACE_SITES`].
//!
//! None of the remaining imprecision can hide a NEW read site in a file that is
//! not already listed, which is the property the tests are for.
//!
//! # How to use it
//!
//! When the test fails, do not widen the table to make it pass. Read the new
//! site, decide whether the invariant of the lane ("opaque evidence and status
//! labels are not proof authority") holds there, write that down in the row's
//! `note`, and only then record the site.

/// What KIND of producer datum a row names, which decides how the read-site scan
/// looks for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProducerFieldKind {
    /// A named field of a producer STRUCT, read as `.field`. The scan cannot
    /// attribute these by type (see the module docs).
    StructField,
    /// A named producer member read as the exact path `Type::Member`: an enum
    /// variant or an uppercase associated constant, in a pattern, construction
    /// or comparison. This is how a `trust_ir` enum's
    /// payload is actually read here (`Inst::Call { callee, .. }` binds `callee`
    /// without ever writing `.callee`), so the scan looks for the PATH and the
    /// attribution is exact.
    NamedPath,
}

/// One producer field, its read sites in this crate, and what the lane does
/// with it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerField {
    /// The `trust_ir` type the field belongs to.
    pub ty: &'static str,
    /// The field name, or — for [`ProducerFieldKind::NamedPath`] — the member
    /// name.
    pub field: &'static str,
    /// Whether this row names a struct field or an enum variant.
    pub kind: ProducerFieldKind,
    /// Files under `crates/trust-vc-trust-engine/src/` that read it, relative to
    /// that directory. Empty means NOT READ by this crate.
    pub read_sites: &'static [&'static str],
    /// What the lane does with it, and whether the invariant holds there.
    pub note: &'static str,
}

/// EVERY FILE THAT WRITES `Type { .. }` FOR A PRODUCER STRUCT.
///
/// ROUND 9's correction to this module's own measurement. The docs used to say
/// "MEASURED at the time of writing: this crate contains no destructuring
/// pattern for any producer type", and that was FALSE and load-bearing: the
/// crate holds about forty `Type::Variant { field, .. }` patterns, and one
/// (`Inst::Call { callee, .. }`) was added by the very commit that wrote the
/// sentence. A destructuring pattern reads a field without writing `.field`, so
/// it is invisible to the field-access scan.
///
/// Enum variants are now scanned by PATH ([`ProducerFieldKind::NamedPath`]),
/// which sees those patterns. This table closes the remaining half — a brace
/// after a producer STRUCT's name. It is deliberately CRUDE: it cannot tell a
/// pattern from a construction, so a file that merely BUILDS a fixture appears
/// here too, and a `fn … -> Module {` signature counts as a brace as well. That
/// costs a one-time disposition and buys the property that matters: a new
/// destructuring of a producer struct fails the ratchet — ROUND 11: in a NEW
/// file or in one ALREADY LISTED, because what is compared is the per-file
/// COUNT, not the set of files.
///
/// MEASURED when the counts were first recorded (round 11): every brace the
/// scan reports is a construction or a signature position, and not one is a
/// destructuring pattern. That is what makes the recorded numbers a baseline
/// rather than an accepted debt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerTypeBraceSites {
    /// The producer struct.
    pub ty: &'static str,
    /// Every file whose code writes `<ty> {` — pattern or construction — with
    /// HOW MANY times it does.
    pub sites: &'static [ProducerTypeBraceSite],
}

/// One file's brace sites for one producer struct, COUNTED.
///
/// ROUND 11's second census gap. The ratchet used to compare the SET of files,
/// so a NEW destructure in a file the table already listed was invisible —
/// measured by probe R10-P6, which added
/// `let NativeObligationSource { span, facts, .. } = source` to
/// `native_assertion_id.rs`, a file already listed for that very type, and
/// passed all four census tests. The count is the cheapest thing that sees it:
/// a second brace in a listed file moves 1 to 2.
///
/// It is deliberately CRUDE in the same way the file list was: it cannot tell a
/// pattern from a construction, so adding a fixture-building brace costs a
/// one-time disposition too. That is the trade the module already made.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerTypeBraceSite {
    /// The file, relative to `src/`.
    pub file: &'static str,
    /// How many `<ty> {` occurrences its CODE contains.
    pub braces: usize,
}

/// Brace sites for every tabled producer STRUCT.
pub const PRODUCER_TYPE_BRACE_SITES: &[ProducerTypeBraceSites] = &[
    // The Box types are only constructed by the named-refusal control; no
    // production path destructures their evidence. These are measured braces.
    ProducerTypeBraceSites {
        ty: "BoxValidityFact",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "BoxFactSession",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "BoxDerefSite",
        sites: &[ProducerTypeBraceSite {
            file: "trust_ir_body/check.rs",
            braces: 2,
        }],
    },
    ProducerTypeBraceSites {
        ty: "Module",
        sites: &[
            // The seventh is the `fn inc_with(node) -> Module {` signature of
            // the tensor declines' `#[cfg(test)]` fixture builder. Not a
            // pattern.
            ProducerTypeBraceSite {
                file: "native_discharge/body.rs",
                braces: 7,
            },
            ProducerTypeBraceSite {
                file: "native_discharge/ty.rs",
                braces: 1,
            },
            // The `fn one_instruction_module(node) -> Module {` signature of
            // the advisory lane's `#[cfg(test)]` fixture builder. Not a
            // pattern.
            ProducerTypeBraceSite {
                file: "trust_ir_body/check.rs",
                braces: 1,
            },
            // MERGED 2026-09-23: the `fn every_admitted_shape() -> Module {`
            // signature of the advisory lane's `#[cfg(test)]` fixture builder.
            // Read, not a pattern.
            ProducerTypeBraceSite {
                file: "trust_ir_body/lower.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "Function",
        sites: &[
            ProducerTypeBraceSite {
                file: "lib.rs",
                braces: 1,
            },
            // MERGED 2026-09-23: `module.functions.push(Function {` in the
            // advisory lane's `#[cfg(test)]` fixture builder — a construction.
            // `module.functions.push(Function {` in `check.rs`'s `#[cfg(test)]`
            // fixture — a construction.
            ProducerTypeBraceSite {
                file: "trust_ir_body/check.rs",
                braces: 1,
            },
            ProducerTypeBraceSite {
                file: "trust_ir_body/lower.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "Block",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "CoverageAssurance",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "SpecObligationRef",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "InstrNode",
        // MERGED 2026-09-23: the `fn node(..) -> InstrNode {` signature of the
        // advisory lane's `#[cfg(test)]` fixture builder. Read, not a pattern.
        // In `check.rs`, the `fn admitted_const() -> InstrNode {` signature of
        // the tensor refusals' `#[cfg(test)]` twin builder. Not a pattern.
        sites: &[
            ProducerTypeBraceSite {
                file: "trust_ir_body/check.rs",
                braces: 1,
            },
            ProducerTypeBraceSite {
                file: "trust_ir_body/lower.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "ProofObligation",
        sites: &[
            ProducerTypeBraceSite {
                file: "native_assertion_id.rs",
                braces: 1,
            },
            // The coverage unit tests' fixture builder: the signature
            // `fn obligation(id, formula) -> ProofObligation {` and the
            // construction it returns.
            ProducerTypeBraceSite {
                file: "native_coverage/tests.rs",
                braces: 2,
            },
            ProducerTypeBraceSite {
                file: "native_discharge/body.rs",
                braces: 1,
            },
            // The `#[cfg(test)]` import-gate fixture: the signature
            // `fn obligation(kind) -> ProofObligation {` and the construction
            // it returns.
            ProducerTypeBraceSite {
                file: "native_trust_ir_bundle.rs",
                braces: 2,
            },
            // A PATTERN: `obligation_refusal` destructures every field with no
            // `..`, so a field trust-ir adds fails to compile there. It reads
            // `kind`, `function`, `site` and `spec` (a `spec` is refused); the
            // status, description, formula and source are bound to `_`.
            ProducerTypeBraceSite {
                file: "trust_ir_body/mod.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "ObligationSite",
        // Every one a construction in a `#[cfg(test)]` fixture.
        sites: &[ProducerTypeBraceSite {
            file: "native_discharge/body.rs",
            braces: 8,
        }],
    },
    ProducerTypeBraceSites {
        ty: "ProofFormula",
        sites: &[
            ProducerTypeBraceSite {
                file: "native_assertion_id.rs",
                braces: 1,
            },
            // The signature `fn formula(..) -> ProofFormula {` of the coverage
            // unit tests' fixture builder. Not a pattern.
            ProducerTypeBraceSite {
                file: "native_coverage/tests.rs",
                braces: 1,
            },
            ProducerTypeBraceSite {
                file: "native_discharge/formula.rs",
                braces: 2,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "ProofObligationSourceIdentity",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "PublicObligationIdentity",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "ProofCertificate",
        sites: &[
            ProducerTypeBraceSite {
                file: "native_discharge/body.rs",
                braces: 2,
            },
            ProducerTypeBraceSite {
                file: "native_trust_ir_bundle.rs",
                braces: 2,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "ProofContext",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeCompilerFacts",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeObligationSource",
        sites: &[ProducerTypeBraceSite {
            file: "native_assertion_id.rs",
            braces: 2,
        }],
    },
    ProducerTypeBraceSites {
        ty: "TrustVcNativeRequest",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeVerificationBundle",
        // The export seam's unit-test fixture signature
        // `fn corpus_with_bridge_atom() -> NativeVerificationBundle {`.
        sites: &[ProducerTypeBraceSite {
            file: "native_assertion_id.rs",
            braces: 1,
        }],
    },
    ProducerTypeBraceSites {
        ty: "StorageLayout",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "TargetInfo",
        sites: &[
            ProducerTypeBraceSite {
                file: "native_discharge/body.rs",
                braces: 2,
            },
            ProducerTypeBraceSite {
                file: "native_discharge/ty.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "ClosureTy",
        sites: &[ProducerTypeBraceSite {
            file: "native_discharge/body.rs",
            braces: 1,
        }],
    },
    ProducerTypeBraceSites {
        ty: "FuncTy",
        sites: &[
            ProducerTypeBraceSite {
                file: "native_discharge/body.rs",
                braces: 16,
            },
            // MERGED 2026-09-23, both constructions, read: `module.func_types
            // .push(FuncTy {` in the advisory lane's `#[cfg(test)]` fixture
            // builder, and `variant_module.func_types.push(FuncTy {` in its
            // interpreter replay, which builds the entry signature it runs.
            // `module.func_types.push(FuncTy {` in `check.rs`'s `#[cfg(test)]`
            // fixture — a construction.
            ProducerTypeBraceSite {
                file: "trust_ir_body/check.rs",
                braces: 1,
            },
            ProducerTypeBraceSite {
                file: "trust_ir_body/lower.rs",
                braces: 1,
            },
            ProducerTypeBraceSite {
                file: "trust_ir_body/replay.rs",
                braces: 1,
            },
        ],
    },
    ProducerTypeBraceSites {
        ty: "SwitchCase",
        sites: &[ProducerTypeBraceSite {
            file: "native_discharge/body.rs",
            braces: 3,
        }],
    },
    ProducerTypeBraceSites {
        ty: "SourceSpan",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "ProofLineageNode",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "ProofCertificateRef",
        // The coverage unit tests' fixture builder: the signature
        // `fn reference(..) -> ProofCertificateRef {` and the construction it
        // returns.
        sites: &[ProducerTypeBraceSite {
            file: "native_coverage/tests.rs",
            braces: 2,
        }],
    },
    ProducerTypeBraceSites {
        ty: "ProofReplayIdentity",
        sites: &[ProducerTypeBraceSite {
            file: "native_trust_ir_bundle.rs",
            braces: 1,
        }],
    },
    ProducerTypeBraceSites {
        ty: "NativeRequestProvenance",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeReplayContext",
        // The export seam's unit-test helper signature
        // `fn trust_vc_context(..) -> &mut NativeReplayContext {`.
        sites: &[ProducerTypeBraceSite {
            file: "native_assertion_id.rs",
            braces: 1,
        }],
    },
    ProducerTypeBraceSites {
        ty: "NativeReplayAtom",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeEvidenceArtifact",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "NativeToolIdentity",
        sites: &[],
    },
    ProducerTypeBraceSites {
        ty: "TrustVcNativeEvidenceBundle",
        sites: &[ProducerTypeBraceSite {
            file: "native_trust_ir_bundle.rs",
            braces: 1,
        }],
    },
    ProducerTypeBraceSites {
        ty: "ProofDigest",
        sites: &[ProducerTypeBraceSite {
            file: "native_trust_ir_bundle.rs",
            braces: 1,
        }],
    },
];

/// EVERY PLACE THIS CRATE READS A PRODUCER DATUM BY STRING KEY.
///
/// ROUND 12's closure of the FOURTH EVASION. Every other scan in this module
/// measures SYNTAX — `.field`, `Type::Variant`, `Type {` — over sources whose
/// string literals have been blanked out (see `strip_comments_and_strings`, and
/// the reason it exists). A read that goes through JSON therefore has neither a
/// field access nor a brace, and its key is inside a string:
///
/// ```text
/// let value = serde_json::to_value(source).ok()?;
/// value.get("monomorphization")?.as_u64()
/// ```
///
/// MEASURED (round 11's review, evasion 4): that function, added to
/// `native_assertion_id.rs`, passed all five census tests, although the table
/// lists `monomorphization`'s read sites as `native_trust_ir_bundle.rs` alone.
///
/// So the string keys are counted too, in their own table, over sources whose
/// literals are KEPT. What the counts are is deliberately mixed, and every one
/// was read when it was recorded:
///
/// * `native_assertion_id.rs` reads the PRODUCER's payload source record by
///   key. The formula node instead uses the canonical typed serde decoder;
///   its `.formula` access is recorded in the field-read census.
/// * `bin/trust_vc-trust-runner.rs` SNIFFS which input shape a file is, before
///   anything is decoded. It names producer keys without reading a decoded
///   producer value.
/// * `lib.rs` and `mir_memory.rs` read `request.metadata()`, a
///   `BTreeMap<String, String>` whose keys (`producer`, `mir_body`) happen to
///   spell tabled field names, and `mir_memory.rs`'s `#[cfg(test)]` block
///   indexes THIS CRATE's own emitted JSON.
///
/// The scan cannot tell those apart — like the brace-site table, it is crude on
/// purpose. What it buys is that a NEW string-key read of a producer field name
/// cannot appear in any file without a disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerFieldStringKeySites {
    /// The producer field name, as a JSON key.
    pub field: &'static str,
    /// Every file whose code reads that key as a string, with HOW MANY times.
    pub sites: &'static [ProducerFieldStringKeySite],
}

/// One file's string-key reads of one producer field name, COUNTED.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerFieldStringKeySite {
    /// The file, relative to `src/`.
    pub file: &'static str,
    /// How many `get("<field>")` / `get_mut("<field>")` / `["<field>"]` reads
    /// its code contains.
    pub reads: usize,
}

/// String-key reads of every tabled producer field name.
///
/// MEASURED when first recorded (round 12): every site below was read. The
/// export seam's two (`source`, `assertion_id`) read the PRODUCER's payload
/// document; the formula decoder no longer has string-key reads of `formula`
/// or `value`, because it deserializes the original bytes into the canonical
/// typed node. The runner's
/// eight sniff which input shape a file is before anything is decoded; `lib.rs`
/// and `mir_memory.rs` read a `metadata()` map or this crate's OWN emitted JSON
/// in a `#[cfg(test)]` block.
///
/// ROUND 17 adds three export-seam reads, each read when recorded:
/// `native_assertion_id.rs`'s strict payload reader (`read_payload_identity`,
/// `span_not_canonical`) reads the source record's `source_id` and `span`, and
/// the span's `file`, ONLY to check that each has its one accepted type. Their
/// values are never used: a wrong type makes the payload unreadable, which can
/// only WITHDRAW an id (or refuse the bundle beside a compiler fact), never
/// license one.
pub const PRODUCER_FIELD_STRING_KEY_SITES: &[ProducerFieldStringKeySites] = &[
    ProducerFieldStringKeySites {
        field: "assertion_id",
        sites: &[ProducerFieldStringKeySite {
            file: "native_assertion_id.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "file",
        sites: &[ProducerFieldStringKeySite {
            file: "native_assertion_id.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "id",
        sites: &[ProducerFieldStringKeySite {
            file: "mir_memory.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "kind",
        sites: &[ProducerFieldStringKeySite {
            file: "mir_memory.rs",
            reads: 2,
        }],
    },
    ProducerFieldStringKeySites {
        field: "lineage",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "mode",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "module",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "obligations",
        sites: &[
            ProducerFieldStringKeySite {
                file: "bin/trust_vc-trust-runner.rs",
                reads: 2,
            },
            ProducerFieldStringKeySite {
                file: "mir_memory.rs",
                reads: 2,
            },
        ],
    },
    ProducerFieldStringKeySites {
        field: "producer",
        sites: &[ProducerFieldStringKeySite {
            file: "lib.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "requests",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "schema_version",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "source",
        sites: &[ProducerFieldStringKeySite {
            file: "native_assertion_id.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "source_id",
        sites: &[
            ProducerFieldStringKeySite {
                file: "bin/trust_vc-trust-runner.rs",
                reads: 1,
            },
            ProducerFieldStringKeySite {
                file: "mir_memory.rs",
                reads: 1,
            },
            ProducerFieldStringKeySite {
                file: "native_assertion_id.rs",
                reads: 1,
            },
        ],
    },
    ProducerFieldStringKeySites {
        field: "span",
        sites: &[ProducerFieldStringKeySite {
            file: "native_assertion_id.rs",
            reads: 1,
        }],
    },
    ProducerFieldStringKeySites {
        field: "trust_ir_module_digest",
        sites: &[ProducerFieldStringKeySite {
            file: "bin/trust_vc-trust-runner.rs",
            reads: 1,
        }],
    },
];

/// A producer type this crate NAMES but does not table field by field, and why.
///
/// An entry here is a claim that the type carries nothing for the census to say.
/// Each one is checked: the opaque ids are destructured as one-field newtypes by
/// the compile-time ratchet (so a second field breaks the build), and the
/// remaining entry is a unit struct with no fields at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UntabledProducerType {
    /// The `trust_ir` type.
    pub ty: &'static str,
    /// Why it has no rows, and what still ratchets it.
    pub reason: &'static str,
}

/// Producer types deliberately left out of [`PRODUCER_FIELDS`].
pub const UNTABLED_PRODUCER_TYPES: &[UntabledProducerType] = &[
    // MERGED 2026-09-23: the types upstream's ADVISORY body lane
    // (`trust_ir_body/`) names that the `native_discharge` lane did not. Each
    // was read at its use before being listed.
    UntabledProducerType {
        ty: "Interpreter",
        reason: "trust-ir's reference interpreter, CALLED (not read) by `trust_ir_body/replay.rs` to replay a solver witness; producer code, not producer data crossing the seam. Its result only decides whether an advisory refutation is reported as `Refuted`. Its fields are private, so no compile-time destructuring witness is possible.",
    },
    UntabledProducerType {
        ty: "InterpretOptions",
        reason: "The interpreter's option struct, CONSTRUCTED by `trust_ir_body/replay.rs` (`..InterpretOptions::default()`); nothing producer-supplied is read from it.",
    },
    UntabledProducerType {
        ty: "InterpretValue",
        reason: "Witness values CONSTRUCTED by `trust_ir_body/replay.rs` (`InterpretValue::bool` / `::int`) from the solver's own model, to feed the interpreter.",
    },
    UntabledProducerType {
        ty: "FuncAttrs",
        reason: "Only `FuncAttrs::default()`, in the advisory lane's `#[cfg(test)]` fixture builder (`trust_ir_body/lower.rs`); never read.",
    },
    UntabledProducerType {
        ty: "Visibility",
        reason: "Only `Visibility::default()`, in the advisory lane's `#[cfg(test)]` fixture builders (`trust_ir_body/check.rs`, `trust_ir_body/lower.rs`); never read.",
    },
    UntabledProducerType {
        ty: "Linkage",
        reason: "Only `Linkage::default()`, in the advisory lane's `#[cfg(test)]` fixture builder (`trust_ir_body/lower.rs`); never read.",
    },
    UntabledProducerType {
        ty: "ValueId",
        reason: "Opaque one-field newtype id (`pub struct ValueId(pub u32)`); read only through `index()`/`as_usize()`. Witnessed by the compile-time ratchet's `let trust_ir::ValueId(_)`.",
    },
    UntabledProducerType {
        ty: "BlockId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "FuncId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "FuncTyId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "TyId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "ProofId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "ProofLineageId",
        reason: "Opaque one-field newtype id; witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "NativeAssertionId",
        reason: "Opaque one-field newtype id — the EXPORT SEAM's rendering A. What this crate does with its value is the whole of `crate::native_assertion_id`; the id TYPE itself carries nothing more. Witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "NativeReplayAtomId",
        reason: "Opaque one-field newtype id of a replay atom (`pub struct NativeReplayAtomId(pub u32)`). The export seam names an atom by it in a refusal and the unit tests construct atoms with it; it licenses nothing. Witnessed by the compile-time ratchet.",
    },
    UntabledProducerType {
        ty: "RejectingModuleProofAuthority",
        reason: "A unit struct (`pub struct RejectingModuleProofAuthority;`) with no fields. It is named in doc comments only — the read-site scan blanks comments, so it has no code site at all.",
    },
    // trust-ir-build's coverage verdict (`native_coverage.rs`). The report is
    // COMPUTED in this process by `coverage_establishment_report` over the
    // bundle the producer validator already accepted; it is not data the
    // producer wrote, so these are the same kind of entry as `Interpreter`.
    UntabledProducerType {
        ty: "CoverageEstablishmentReport",
        reason: "trust-ir-build's coverage report, COMPUTED in process by `coverage_establishment_report` (`native_coverage.rs`), never decoded from the bundle. Read only through `is_checked`, `for_certificate` and `refusals`; any refusal is fatal for the whole bundle, and an unchecked report establishes nothing. Its fields are private, so no destructure can witness it; the verdicts it returns are witnessed as `CertificateCoverage`.",
    },
    UntabledProducerType {
        ty: "CoverageInputs",
        reason: "Constructed as `CoverageInputs::default()` in `native_coverage.rs`: no attestation, no solved bundles, no replayer, so only basis K can establish coverage. Nothing is read from it.",
    },
];

/// EVERY CRATE THE PRODUCER SPEAKS TO THIS LANE THROUGH.
///
/// ROUND 11. The type-closure ratchet scanned `trust_ir::` alone, so
/// `trust_ir_build` — the producer's own VALIDATOR, whose `ValidationError` this
/// lane destructures to carry an upstream refusal past the input gate — was
/// outside the census entirely. A producer crate this lane names but does not
/// list here is a census hole by construction, so the list is short and the
/// scan is over-approximating on purpose.
pub const PRODUCER_CRATES: &[&str] = &["trust_ir", "trust_ir_build"];

/// The path roots that name THIS crate, for the alias scan.
///
/// ROUND 13. An alias of an alias spelled through one of these — `type A =
/// trust_ir_build::ValidationError; type B = self::A;` — was invisible to all
/// six ratchets: the alias fixpoint chased BARE names only, and a path root
/// outside [`PRODUCER_CRATES`] resolved to nothing. These roots cannot reach
/// another crate's type, so a segment under one is resolved the same way a bare
/// name is.
pub const LOCAL_PATH_ROOTS: &[&str] = &["self", "crate", "super"];

/// Every producer type either ratchet pins, tabled or excluded.
pub const PINNED_PRODUCER_TYPES: &[&str] = &[
    "BoxPointee",
    "BoxValidityFact",
    "BoxDerefSite",
    "BoxFactSession",
    "PremiseRoot",
    "Module",
    "Function",
    "Block",
    "InstrNode",
    "ProofObligation",
    "ObligationSite",
    "ProofFormula",
    "ProofObligationSourceIdentity",
    "PublicObligationIdentity",
    "ProofCertificate",
    "ProofContext",
    "NativeCompilerFacts",
    "NativeObligationSource",
    "TrustVcNativeRequest",
    "NativeVerificationBundle",
    "TargetInfo",
    "StorageLayout",
    "Inst",
    "Ty",
    "Constant",
    "ProofEvidence",
    "NativeVerificationBundleError",
    "NativeCompilerFactRef",
    "NativeAdapterInput",
    "NativeVerificationRequest",
    "ObligationKind",
    "ProofStatus",
    "NativeObligationCause",
    "TrustVcVerificationMode",
    "NativeVerifierSuite",
    "NativeEvidenceArtifactKind",
    "NativeBundleProducer",
    "CallingConv",
    "Endianness",
    "StructPassingPolicy",
    "BinOp",
    "UnOp",
    "ICmpOp",
    "OverflowOp",
    "CastOp",
    "FuncTy",
    "ClosureTy",
    "SwitchCase",
    "SourceSpan",
    "ProofLineageNode",
    "ProofCertificateRef",
    "ProofReplayIdentity",
    "NativeRequestProvenance",
    "NativeEvidenceArtifact",
    "NativeToolIdentity",
    "TrustVcNativeEvidenceBundle",
    "ProofDigest",
    "ValueId",
    "BlockId",
    "FuncId",
    "FuncTyId",
    "TyId",
    "ProofId",
    "ProofLineageId",
    "NativeAssertionId",
    "RejectingModuleProofAuthority",
    "ValidationError",
    // MERGED 2026-09-23: named by upstream's ADVISORY body lane (`trust_ir_body/`).
    "Interpreter",
    "InterpretOptions",
    "InterpretValue",
    "InterpretErrorCode",
    "FuncAttrs",
    "Linkage",
    "ProofDigestAlgorithm",
    "CoverageAssurance",
    "CoverageBound",
    "SpecObligationRef",
    "TrustMcVerificationMode",
    "TrustWpVerificationMode",
    "TrustWpFramePolicy",
    "TrustWpLoopStrategy",
    "Visibility",
    // trust-ir-build's in-process coverage verdict (`native_coverage.rs`).
    "CoverageEstablishmentReport",
    "CoverageInputs",
    "CertificateCoverage",
    "CoverageBasis",
    "CoverageUndeterminedReason",
    "KernelClaimFamily",
    // A drop's glue, resolved for call attribution (`native_discharge/body.rs`).
    "DropResolution",
    // A clause binding's sort, read by coverage rule 5 (`native_coverage.rs`).
    "ClauseSort",
    // The citing TrustVc request's replay atoms: rendering E of the assertion
    // identity, read by the export seam (`native_assertion_id.rs`).
    "NativeReplayContext",
    "NativeReplayAtom",
    "NativeReplayAtomKind",
    "NativeReplayAtomId",
];

/// THE TABLE. Derived, not written: see the module docs.
pub const PRODUCER_FIELDS: &[ProducerField] = &[
    ProducerField {
        ty: "BoxPointee",
        field: "Sized",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "CONSTRUCTED only for the BoxDeref negative fixture, with U8. The production checker refuses the entire instruction and never derives an access or a validity fact from this payload.",
    },
    ProducerField {
        ty: "PremiseRoot",
        field: "ParamByValue",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "CONSTRUCTED only by the named-premise negative fixture; no premise is promoted to established validity.",
    },
    ProducerField {
        ty: "PremiseRoot",
        field: "AllocPostcondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. BoxDeref is refused without inspecting any premise root or strengthening its authority.",
    },
    ProducerField {
        ty: "PremiseRoot",
        field: "ReturnedBoxDischarged",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. BoxDeref is refused without inspecting any premise root or strengthening its authority.",
    },
    ProducerField {
        ty: "PremiseRoot",
        field: "ReturnedBoxAssumed",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. BoxDeref is refused without inspecting any premise root or strengthening its authority.",
    },
    ProducerField {
        ty: "PremiseRoot",
        field: "ReferenceArgBoxValid",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. BoxDeref is refused without inspecting any premise root or strengthening its authority.",
    },
    ProducerField {
        ty: "BoxFactSession",
        field: "PROOF_SNAPSHOT",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "Associated constant, recorded by the same uppercase-path scan as enum variants. It is only a constructor input in the negative fixture, never a licence to lower BoxDeref or claim a verified allocation.",
    },
    ProducerField {
        ty: "BoxValidityFact",
        field: "site",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier. Listed files are the existing field-name union for other producer data: obligation/callee source sites, not Box cast sites.",
    },
    ProducerField {
        ty: "BoxValidityFact",
        field: "session",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "BoxValidityFact",
        field: "evidence",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/check.rs"],
        note: "Only the negative Box refusal fixture clears this evidence vector. Both complete and missing-evidence facts are refused as unsupported; no conjunct, premise or certificate is admitted. The read sites are the conservative evidence-name union across types.",
    },
    ProducerField {
        ty: "BoxValidityFact",
        field: "not_claimed",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "BoxDerefSite",
        field: "item",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "BoxDerefSite",
        field: "ordinal",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "BoxFactSession",
        field: "judged",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "BoxFactSession",
        field: "producing",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ from this Box carrier. The checker refuses BoxDeref before inspecting its validity payload; only the negative fixture constructs the canonical carrier.",
    },
    ProducerField {
        ty: "Module",
        field: "name",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/lower.rs"],
        note: "Named in refusals and in the bundle report. Identity only; licenses no fact. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Module",
        field: "functions",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "E1/E9 resolve the requested function and every callee by `FuncId`; also scanned for the recursion check. ROUND 15: `native_assertion_id.rs` (`AssertionIdIndex::of`) reads every function's summary clauses through trust-ir's own inventory `Module::stated_formulas_iter`, a METHOD CALL, so no `.field` scan in this module can see that site; it is recorded here by hand. What it reads is every stated formula's payload source record (`native_assertion_id`, `assertion_id`), and the read can only WITHDRAW a license: a number such a formula renders publishes no id unless the formula is exactly an obligation's own, and an unreadable rendering withdraws every id in the bundle. It never licenses an id, grounds a formula or feeds a proof. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `trust_ir_body/check.rs` only pushes into it, in its `#[cfg(test)]` fixture; `trust_ir_body/binding.rs` also walks it in `wire_identity_gap`, which only asks trust-ir whether the module has a canonical image.",
    },
    ProducerField {
        ty: "Module",
        field: "structs",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. The `RequestReportInputs::module` doc claimed it was until round 8; the derived scan says otherwise. Every aggregate type declines in `TypeDecoder::sort` before a struct definition is ever needed.",
    },
    ProducerField {
        ty: "Module",
        field: "enums",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ, for the same reason as `structs`.",
    },
    ProducerField {
        ty: "Module",
        field: "records",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Module",
        field: "closure_types",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Module",
        field: "globals",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Module",
        field: "func_types",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "E23 — the DECLARED signature every sort in the lane comes from. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `trust_ir_body/check.rs` only pushes into it, in its `#[cfg(test)]` fixture.",
    },
    ProducerField {
        ty: "Module",
        field: "types",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs"],
        note: "NOT READ. The listed site is `self.types`, the lane's own `TypeDecoder`.",
    },
    ProducerField {
        ty: "Module",
        field: "proof_obligations",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "E2/E5/E10/E21 and the export seam's bundle-wide injection scan. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_coverage.rs` walks it once per bundle for coverage rule 5, keyed by id; an id stated twice is a defect.",
    },
    ProducerField {
        ty: "Module",
        field: "proof_certificates",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "E12 — the lineage binding behind `established_callee_ensures`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Module",
        field: "target_info",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs"],
        note: "E16 — the `usize`/`isize` width. An unusable value declines.",
    },
    ProducerField {
        ty: "Module",
        field: "files",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Module",
        field: "obligation_diagnostics",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Module",
        field: "spec_modules",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ as a specification. ROUND 15: `native_assertion_id.rs` (`AssertionIdIndex::of`) reads each machine's typed invariants and temporal formulas through trust-ir's own inventory `Module::stated_formulas_iter`, a METHOD CALL, so no `.field` scan in this module can see that site; it is recorded here by hand. What it reads is every stated formula's payload source record (`native_assertion_id`, `assertion_id`), and the read can only WITHDRAW a license: a number such a formula renders publishes no id unless the formula is exactly an obligation's own, and an unreadable rendering withdraws every id in the bundle. It never licenses an id, grounds a formula or feeds a proof.",
    },
    ProducerField {
        ty: "Module",
        field: "universes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Module",
        field: "predicates",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Module",
        field: "global_asm",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Module-level assembly text trust-ir attaches no semantics to; neither lane models assembly, and nothing here licenses a fact.",
    },
    ProducerField {
        ty: "Module",
        field: "imports",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. The cross-crate import table; neither lane resolves an import, so no fact about another crate enters a verdict.",
    },
    ProducerField {
        ty: "Module",
        field: "tuple_layouts",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Tuple memory layouts; neither lane models memory layout.",
    },
    ProducerField {
        ty: "Module",
        field: "completeness",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ as a fact. The producer's completeness claim for the module. It has no binary wire carrier at the pinned rev, so `trust_ir_body/binding.rs` asks trust-ir's own `Module::completeness_claim_unencodable` and REFUSES a module carrying one (no wire identity); nothing reads the claim's rows.",
    },
    ProducerField {
        ty: "Module",
        field: "drop_glue",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ as a field. `native_discharge/body.rs` (`direct_callee`) asks trust-ir's own `Module::drop_glue_for`, a METHOD CALL no `.field` scan sees, which glue a `Drop` or `DropInvoke` calls; the answer attributes a precondition anchored at the drop to that glue and adds the glue to the recursion walk, and can license no fact. Its `#[cfg(test)]` fixtures write rows through `Module::set_drop_glue`.",
    },
    ProducerField {
        ty: "Module",
        field: "closure_layouts",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Declared closure frames (size, alignment, capture offsets). Neither lane models memory layout or applies a closure: a `Ty::Closure` has no sort in `native_discharge/ty.rs`, and a `CallIndirect` over a closure callee (the application a coherent frame makes codegen-legal) is declined by the native lane and refused by name in `trust_ir_body/check.rs`, whatever the frame says. The table is checked by trust-ir itself (the binary reader and `validate_module`, the P1 input gate), and the advisory digest in `trust_ir_body/binding.rs` keeps it, so a changed frame moves that digest.",
    },
    ProducerField {
        ty: "Module",
        field: "blobs",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "REFUSED BY NAME when non-empty; no row is read. trust-ir wire v70's weight blob table: the bytes a `Constant::TensorBlob` names by digest. Neither lane has a tensor sort, so `native_discharge/body.rs` (`lower_body`) declines a module carrying any row, naming `Module.blobs`, and `trust_ir_body/check.rs` (`check_function`) refuses it as `UnsupportedModuleTable { table: \"Module.blobs\" }`, both before any body is read and whether or not the function cites a row. Only `is_empty` and `len` (for the message) are read, so no blob byte can reach a relation, a query or a replay. `#[cfg(test)]` fixtures in both files pin each refusal against a twin without the row. The advisory digest in `trust_ir_body/binding.rs` clones the module and so keeps the table, but a module carrying one is refused before any verdict is bound to it.",
    },
    ProducerField {
        ty: "Function",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Compared, never trusted: E9 resolves a callee by id. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "name",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/lower.rs"],
        note: "E24 — messages, premise text and assumption-name prefixes ONLY. Never resolves a callee. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `trust_ir_body/binding.rs` uses it only to name the location of a wire-identity refusal.",
    },
    ProducerField {
        ty: "Function",
        field: "ty",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "E23 — the declared signature. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "entry",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "E14 for the CALLEE, and the discharged function's own entry block: the scope a `requires` resolves against. A missing entry block declines. `native_assertion_id.rs` is a FALSE POSITIVE of the union-by-name rule — the site there is `BTreeMap::entry`, not `Function::entry`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). The `native_coverage.rs` site is the same false positive: `BTreeMap::entry` in `formula_defects`.",
    },
    ProducerField {
        ty: "Function",
        field: "blocks",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "The BODY the lane proves from, for the discharged function, plus the callee's entry for contract rebinding, plus the round-8 call-site resolution. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_discharge/mod.rs` (`site_is_the_only_return`) counts the function's `Return` terminators to bind a requested postcondition's site; it reads no fact from them.",
    },
    ProducerField {
        ty: "Function",
        field: "proofs",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "calling_conv",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Function",
        field: "linkage",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "Function",
        field: "attrs",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ — and this is the `body_opacity` gap: at this pin `FuncAttrs` carries no opacity marker, which is WHY callees are contract-only.",
    },
    ProducerField {
        ty: "Function",
        field: "summary",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "NOT READ as a contract. The listed site is trust-vc's own `.summary`. ROUND 15: `native_assertion_id.rs` (`AssertionIdIndex::of`) reads its `requires`, `ensures` and `decreases` clauses through trust-ir's own inventory `Module::stated_formulas_iter`, a METHOD CALL, so no `.field` scan in this module can see that site; it is recorded here by hand. What it reads is every stated formula's payload source record (`native_assertion_id`, `assertion_id`), and the read can only WITHDRAW a license: a number such a formula renders publishes no id unless the formula is exactly an obligation's own, and an unreadable rendering withdraws every id in the bundle. It never licenses an id, grounds a formula or feeds a proof. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "producer",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "NOT READ. The listed sites are `NativeVerificationBundle::producer` and trust-vc's own producer labels.",
    },
    ProducerField {
        ty: "Function",
        field: "value_names",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/binding.rs"],
        note: "E13 — the producer's names, through which a callee clause is rebound. A reserved or duplicate name declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "scopes",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "source_provenance",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Function",
        field: "body_gate",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Codegen authority metadata (whether a backend may emit this body); it says nothing about what the body computes, and no verdict depends on it.",
    },
    ProducerField {
        ty: "Function",
        field: "display_path",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. A human-readable def-path; trust-ir defines it as never proof-bearing.",
    },
    ProducerField {
        ty: "Function",
        field: "section",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. The output section for the function's code; no semantics.",
    },
    ProducerField {
        ty: "Function",
        field: "visibility",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Symbol visibility; no semantics. Only the advisory lane's `#[cfg(test)]` fixture builders construct it (`Visibility::default()`).",
    },
    ProducerField {
        ty: "Function",
        field: "retained",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. `#[used]`-style retention; no semantics.",
    },
    ProducerField {
        ty: "Block",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "The block key; a duplicate declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Block",
        field: "params",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "Block parameters are the phi targets; edge-keyed arguments bind to them. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Block",
        field: "body",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "The instruction sequence, including the terminator-position check. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_discharge/mod.rs` (`site_is_the_only_return`) finds the `Return` terminators to bind a requested postcondition's site; it reads no fact from them.",
    },
    ProducerField {
        ty: "InstrNode",
        field: "inst",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Every modelled instruction; an unmodelled one declines BY NAME. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `trust_ir_body/binding.rs` reads it only in `wire_identity_gap`, to ask trust-ir's own `binary_wire_gap` probe whether the module can be hashed; the answer can only refuse. `native_discharge/mod.rs` (`site_is_the_only_return`) matches `Inst::Return` only, to bind a requested postcondition's site.",
    },
    ProducerField {
        ty: "InstrNode",
        field: "results",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/replay.rs"],
        note: "The values an instruction defines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "InstrNode",
        field: "proofs",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "InstrNode",
        field: "span",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs"],
        note: "NOT READ. The listed sites are `NativeObligationSource::span` and the MIR adapter's own spans. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "InstrNode",
        field: "proof_context",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ — and it is the producer's own per-call-site proof transfer (`assumes`/`establishes`). Naming it here is the point of a DERIVED table: it is the most obvious unread producer claim at this seam, and reading it would be a change of its own (it is a producer CLAIM about which obligations a call discharges, so it could only ever ADD refusals, never license an import).",
    },
    ProducerField {
        ty: "InstrNode",
        field: "scope",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/formula.rs", "native_discharge/mod.rs", "trust_ir_body/binding.rs"],
        note: "NOT READ. The listed sites are the lane's own `Scope` type. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "E21 — identity only. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_coverage.rs` keys the rule-5 formula defects by it.",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "kind",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "E4 on the requested row, E10a on a callee row. Every kind has a written rule; an unknown kind refuses. ROUND 9 added `native_assertion_id.rs`: the kind is cross-checked there against its SECOND producer rendering, the compiler fact's `cause`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "status",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "E6 (def-site `requires`: deliberately NOT read) and E11 (imported `ensures`: `Certified` only, plus evidence). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "description",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "E20 CORRECTED: not read by the LANE, but COPIED VERBATIM onto the produced evidence row by `evidence_row`. It decides nothing and is republished as the producer's own words.",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "formula",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/formula.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "E8/E19 — the predicate, through the single `decode_predicate` door. `native_discharge/formula.rs` reads the typed payload envelope's `.formula` field after deserializing the original bytes with the canonical IR codec. This is the same producer predicate, not a license or an imported assumption: the single-rendering gate remains mandatory, malformed or missing nodes decline, and declared scope and arithmetic semantics are checked during lowering. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_coverage.rs` reads it for coverage rule 5 (an obligation with no formula is undetermined).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "function",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "E2/E5/E10 and round 8's `RowAttribution`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "source",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs"],
        note: "E22, the unit id, and the export seam's rendering B. `native_artifact.rs` is a FALSE POSITIVE of the union-by-name rule — the site there is `TrustVcNativeAssertionIdRendering::source`, this crate's own label for WHERE a rendering came from.",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "site",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "E3 on the requested row (a postcondition is decided only when sited at the function's one `Return`; any other site declines); round 8's positive call-site rule on a callee row. MERGED 2026-09-23, upstream's ADVISORY body lane: `native_trust_ir_bundle.rs` gains it from the advisory entry `discharge_native_trust_ir_request` (the scope gate that REFUSES an obligation not sited in the named function) and from wire rendering of the lane's own `AssertPosition`; `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofObligation",
        field: "spec",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The temporal property an obligation would be attributed to. It is never read as a fact; it only REFUSES. `native_trust_ir_bundle.rs` (`importable_obligation_kind`) refuses an imported or produced certificate for an obligation carrying one, because the report cannot state that attribution, and `trust_ir_body/mod.rs` (`obligation_refusal`, a destructuring pattern recorded in `PRODUCER_TYPE_BRACE_SITES`) refuses to answer such an obligation.",
    },
    ProducerField {
        ty: "ObligationSite",
        field: "function",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "`RowAttribution` and the round-8 call-site resolution. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ObligationSite",
        field: "block",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_scalar_cast.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "Round 8: resolves the site to an instruction. MERGED 2026-09-23, upstream's ADVISORY body lane: `native_trust_ir_bundle.rs` gains it from the advisory entry `discharge_native_trust_ir_request` (the scope gate that REFUSES an obligation not sited in the named function) and from wire rendering of the lane's own `AssertPosition`; `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_discharge/mod.rs` (`site_is_the_only_return`) resolves a REQUESTED postcondition's site and decides the row only when the site is the function's one `Return` terminator; any other site declines. native_scalar_cast.rs retains the original lowering site for exact data matching only; changing it cannot alter the native verdict or issue a translation/source grade.",
    },
    ProducerField {
        ty: "ObligationSite",
        field: "inst_index",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "Round 8: resolves the site to an instruction. MERGED 2026-09-23, upstream's ADVISORY body lane: `native_trust_ir_bundle.rs` gains it from the advisory entry `discharge_native_trust_ir_request` (the scope gate that REFUSES an obligation not sited in the named function) and from wire rendering of the lane's own `AssertPosition`; `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_discharge/mod.rs` (`site_is_the_only_return`) resolves a REQUESTED postcondition's site and decides the row only when the site is the function's one `Return` terminator; any other site declines.",
    },
    ProducerField {
        ty: "ProofFormula",
        field: "schema",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/formula.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs"],
        note: "E8 — an unknown schema declines; also copied onto the evidence row. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_coverage.rs` reads it for coverage rule 5: only an `smtlib2` payload is a text a kernel replay grounds; any other schema leaves coverage undetermined.",
    },
    ProducerField {
        ty: "ProofFormula",
        field: "payload",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/formula.rs", "native_discharge/unit.rs", "native_trust_ir_bundle.rs"],
        note: "E8 — decoded; also hashed into `formula_payload_sha256`. `native_coverage.rs` reads it for coverage rule 5, as a refusal gate only: it is handed to trust-ir's own SMT-LIB2 reader (`spec_surface::check_linked_invariant`, over the clause's own bindings) and compared byte for byte with `smtlib`; this crate keeps no byte rules and parses nothing itself. `native_assertion_id.rs` parses it as JSON under the two schemas that render an assertion identity, only to read that identity: a rendering that disagrees refuses the bundle, and one that cannot be read refuses beside a compiler fact and otherwise withdraws every id. Since round 17 the reader is STRICT: each schema accepts exactly one shape (the module docs write it down), and anything else is unreadable (not JSON, a key repeated inside one object, a document that is not an object, an identity key outside the source record, a key the shape does not have, a value of the wrong type). Since round 15 it reads every formula the module states this way, not only obligation and atom formulas. It never licenses an id.",
    },
    ProducerField {
        ty: "ProofFormula",
        field: "smtlib",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_coverage/tests.rs", "native_discharge/body.rs", "native_discharge/formula.rs"],
        note: "E19 — the second rendering. Absent, or byte-identical to `payload`, or DECLINE. `native_coverage.rs` reads it for coverage rule 5: a rendering that differs from the payload leaves coverage undetermined; `native_coverage/tests.rs` builds fixtures with it. `native_assertion_id.rs` writes it only in its unit tests, to forge an atom's rendering.",
    },
    ProducerField {
        ty: "ProofFormula",
        field: "sort",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_coverage.rs", "native_coverage/tests.rs", "native_discharge/body.rs", "native_discharge/formula.rs", "native_discharge/ty.rs", "native_trust_ir_bundle.rs"],
        note: "E20 CORRECTED: not read by the LANE (every sort comes from the declared signature), but COPIED VERBATIM onto the evidence row by `evidence_row`. `native_coverage.rs` reads it for coverage rule 5: a sort other than `Bool` leaves coverage undetermined; `native_coverage/tests.rs` builds fixtures with it.",
    },
    ProducerField {
        ty: "ProofFormula",
        field: "bindings",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_coverage.rs", "native_scalar_cast.rs"],
        note: "trust-ir's typed meaning of a clause's free names (sort and IR place). `native_coverage.rs` (coverage rule 5) reads each binding's NAME and SORT to build the environment trust-ir's reader reads the payload over (`linked_var_env`); the PLACE is not read there — basis K's kernel replay, via trust-ir's grounder, binds it. Rule 5 only refuses. Neither discharge lane reads it: `native_discharge` binds a payload's names by its own convention and `trust_ir_body` never reads a formula, so a clause whose producer bindings disagree with that convention is not detected by those lanes; that remains an open gap, not a checked property. The native_scalar_cast.rs union site is a same-name field in the bounded unbound-data observation sink; it does not read producer bindings or grant native verdict/proof authority.",
    },
    ProducerField {
        ty: "ProofObligationSourceIdentity",
        field: "source_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "trust_ir_adapter.rs"],
        note: "NOT READ by the trust-ir lane. The listed sites are trust-vc's own `source_id`.",
    },
    ProducerField {
        ty: "ProofObligationSourceIdentity",
        field: "assertion_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "THE EXPORT SEAM's rendering B. Round 8: no code in `crates/` read it before. ROUND 16: `AssertionIdIndex::of` also reads it as a STRING CLASS: an obligation carries every number its string carries anywhere in the bundle, so an unnumbered obligation sharing a numbered one's string makes that number ambiguous. The read can only WITHDRAW a license.",
    },
    ProducerField {
        ty: "ProofObligationSourceIdentity",
        field: "range",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "ProofObligationSourceIdentity",
        field: "public",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs"],
        note: "E22/P6/P7 — the unit id and the semantic digest. ROUND 13: `native_assertion_id.rs` reads it in `AssertionIdIndex::of`, as part of the identity two obligations sharing an assertion number must agree on. The read can only WITHDRAW a license: a number whose carriers differ here publishes no id (`MissingAssertionId`). It never licenses an id the rest of the rule would refuse.",
    },
    ProducerField {
        ty: "PublicObligationIdentity",
        field: "obligation_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "multi_assertion_proof_tests.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/mod.rs", "native_scalar_cast.rs", "native_trust_ir_bundle.rs"],
        note: "P6/E22 — the `vc:` identity taken verbatim as the unit id. `multi_assertion_proof_tests.rs` (test-only) calls the engine's own `TrustProofEvidence::obligation_id()` accessor, not this field; the name scan cannot tell the two apart. ROUND 13: `native_assertion_id.rs` reads it in `AssertionIdIndex::of`, as part of the identity two obligations sharing an assertion number must agree on. The read can only WITHDRAW a license: a number whose carriers differ here publishes no id (`MissingAssertionId`). It never licenses an id the rest of the rule would refuse. The native_scalar_cast.rs union site compares its own private observation/certificate identities. It does not admit a producer label as evidence or change native verdicts or proof grades.",
    },
    ProducerField {
        ty: "PublicObligationIdentity",
        field: "semantic_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "P7 — copied onto a produced certificate and LABELLED the producer's claim. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofCertificate",
        field: "obligation",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "E12 — which row a certificate is bound to. `native_assertion_id.rs` reads `NativeReplayAtom::obligation` (which obligation an atom renders the identity of; see that row).",
    },
    ProducerField {
        ty: "ProofCertificate",
        field: "prover",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "Named in the premise; identity only.",
    },
    ProducerField {
        ty: "ProofCertificate",
        field: "evidence",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/check.rs"],
        note: "E12 and the round-8 MINOR: the `CleanCic` term and lineage the premise quotes. The field-name union includes trust_ir_body/check.rs because its negative fixture clears BoxValidityFact evidence, not ProofCertificate evidence; the instruction remains unsupported.",
    },
    ProducerField {
        ty: "ProofCertificate",
        field: "assurance",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ by this crate. Release admission derives coverage from the kernel replay of the certificate itself (basis K, `native_coverage.rs`) and never reads the in-module row. trust-ir-build's `coverage_establishment_report` reads it, and REFUSES a row claiming more than the certificate's derived bound; `judge_certificate` makes any such refusal fatal for every certificate of the bundle. Certificates this crate mints record `None`.",
    },
    ProducerField {
        ty: "ProofContext",
        field: "assumes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. See `InstrNode::proof_context`.",
    },
    ProducerField {
        ty: "ProofContext",
        field: "establishes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. See `InstrNode::proof_context`.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "adt_layouts",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ (no aggregate type reaches this lane).",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "fat_pointers",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "trait_object_metadata",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "pointer_offsets",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "casts",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_scalar_cast.rs"],
        note: "NOT READ — a `CastOp` is checked against the DECLARED sorts instead. The native_scalar_cast.rs union site is a same-name field containing actual encoder cast emissions, not NativeCompilerFacts casts. It checks availability of unbound observation data only; no producer cast fact is assumed and no native verdict/grade changes.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "monomorphizations",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ as a table; `NativeObligationSource::monomorphization` is republished as an id.",
    },
    ProducerField {
        ty: "NativeCompilerFacts",
        field: "obligation_sources",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "THE EXPORT SEAM's rendering A, plus the compiler-facts binding on every evidence row. ROUND 11 adds `native_assertion_id.rs`: its own `#[cfg(test)]` module builds a one-obligation `NativeCompilerFacts` to drive `validate_assertion_id_renderings` directly, so the site is a test fixture assembling the gate's input, not a new place where a producer claim reaches a verdict.",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "obligation",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The key the source table is joined on. `native_assertion_id.rs` reads `NativeReplayAtom::obligation` (which obligation an atom renders the identity of; see that row).",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "public_obligation_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "CORRECTED, round 9. This row used to say \"republished in the compiler-facts binding\", and that was FALSE for THIS type: `TrustVcNativeCompilerFactsBinding` has no such field. Until round 13 the compiler-fact rendering of the public identity was NOT READ by this crate at all. ROUND 13: `native_assertion_id.rs` reads it in `AssertionIdIndex::of`, as part of the identity two obligations sharing an assertion number must agree on. The read can only WITHDRAW a license: a number whose carriers differ here publishes no id (`MissingAssertionId`). It never licenses an id the rest of the rule would refuse. The `native_trust_ir_bundle.rs` site is the union-by-name imprecision — it is `TrustVcNativeTrustIrDischargeOutcome::public_obligation_id`, which carries the OBLIGATION-side `source.public.obligation_id` instead. Upstream cross-checks the two renderings of the public id itself (an obligation whose embedded public id disagrees with its compiler-fact source row is refused there), which is why the export seam had to repair only the ASSERTION id.",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "function",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "Republished in the compiler-facts binding. NOT used to attribute a row — that is `ProofObligation::function` / `ObligationSite::function`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "span",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs"],
        note: "Republished in the compiler-facts binding; decides nothing. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "assertion_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "THE EXPORT SEAM's rendering A — round 8's blocker. Published only when corroborated.",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "cause",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "Republished in the compiler-facts binding and folded into `obligation_source_digest`. `ProofObligation::kind` stays the authority (E4/E10a) — this is never read AS a kind. CORRECTED, round 9: this row named the hazard (\"a second producer rendering of the kind would be E19's shape again\") and then dispositioned it as `NOT read`, which is the same \"the lane does not consult it\" answer E20's `formula.sort` had to be corrected for — the blocker was about what the lane PUBLISHES. The two renderings are now cross-checked at the input gate (`validate_obligation_kind_renderings`), refusing the flat contradictions only.",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "monomorphization",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Republished in the compiler-facts binding; identity only.",
    },
    ProducerField {
        ty: "NativeObligationSource",
        field: "facts",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Republished in the compiler-facts binding; `MissingCompilerFactReferences` requires it non-empty. Their CONTENT is not read.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Names the request in the report. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "mode",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_trust_ir_bundle.rs"],
        note: "P4 — selects the arm; each arm mints only its own verdicts.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "obligations",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_assertion_id.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "WHICH ROWS ARE ANSWERED. Round 8 named this as missing from the hand-written list: it is a producer field, and the lane answers exactly the rows it lists. It can only narrow what is answered — a row it omits gets no outcome and no certificate — so it cannot manufacture a verdict; it is listed because an unlisted producer field is an unexamined one. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_assertion_id.rs` reads `TrustVcNativeRequest::obligations` in the replay-atom input gate: an atom citing an obligation its request does not list refuses the bundle.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "certificates",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "P5 — graded on import; DROPPED entirely on the discharge lane.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "lineage_roots",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Bounds the lineage walk for replay metadata; republished.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "options",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. A TrustVc request's options carry no authority here, and no other request's options are read either: coverage is basis K, not a bound derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "diagnostics",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs"],
        note: "NOT READ. The listed site is trust-vc's own `.diagnostics`.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "provenance",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "Suite and replay metadata for the evidence row; graded, never proof authority. `native_assertion_id.rs` reads `TrustVcNativeRequest::provenance` for the request's replay context (rendering E of the assertion identity); it licenses an id, never a fact.",
    },
    ProducerField {
        ty: "TrustVcNativeRequest",
        field: "function",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/binding.rs", "trust_ir_body/mod.rs"],
        note: "E1 — positively required. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "schema_version",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "trust_ir_adapter.rs"],
        note: "Validated upstream.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "producer",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Republished as a label.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "input",
        kind: ProducerFieldKind::StructField,
        read_sites: &["bin/trust_vc-trust-runner.rs", "native_trust_ir_bundle.rs"],
        note: "Republished as the input kind/digest.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "provenance",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "NOT READ. The listed site is `TrustVcNativeRequest::provenance`. `native_assertion_id.rs` reads `TrustVcNativeRequest::provenance` for the request's replay context (rendering E of the assertion identity); it licenses an id, never a fact.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "serialization",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "diagnostics",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs"],
        note: "NOT READ. The listed site is trust-vc's own `.diagnostics`.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "trust_ir_module_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Bound onto every evidence row and re-checked against the embedded module upstream.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "compiler_facts",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "The source table and its digest. `native_assertion_id.rs` reads it only in its unit tests, to hand the corpus bundle to the replay-atom input gate.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "module",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_scalar_cast.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "P1 — the module, gated by the producer validator first. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_coverage.rs` reads the module's obligations for coverage rule 5, after the producer validator gate. `native_assertion_id.rs` reads it only in its unit tests, to hand the corpus bundle to the replay-atom input gate. native_scalar_cast.rs retains the complete original module through the canonical writer for optional same-input data matching. It prunes no fields, changes no admission rule, and issues no translation/source proof authority.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "lineage",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_adapter.rs"],
        note: "Replay metadata for an imported certificate.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "requests",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "The requests answered. `native_assertion_id.rs` reads it only in its unit tests, to hand the corpus bundle's requests to the replay-atom input gate.",
    },
    ProducerField {
        ty: "NativeVerificationBundle",
        field: "evidence_bundles",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Release-evidence validation on import.",
    },
    ProducerField {
        ty: "TargetInfo",
        field: "triple",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "TargetInfo",
        field: "pointer_size",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/ty.rs"],
        note: "E16.",
    },
    ProducerField {
        ty: "TargetInfo",
        field: "endianness",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "TargetInfo",
        field: "abi",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "TargetInfo",
        field: "struct_passing",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    // --- Inst ------------------------------------------------------------
    ProducerField {
        ty: "Inst",
        field: "BinOp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "LOWERED. `lower_inst` models it as the SMT operation the `op` names, at the declared width; spec arithmetic at a machine width declines (round 1). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "UnOp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED by `lower_inst`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Overflow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "ICmp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "LOWERED by `lower_inst`; the result sort is `Ty::Bool`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "FCmp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Cast",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED by `lower_inst`, with the `CastOp` modelled faithfully (round 2) — an op it cannot model declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "BoxDeref",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The advisory v0 checker refuses this instruction by name before interpreting its site-bound validity hypothesis. Test-only canonical premise construction grants no established validity, source refinement or proof grade.",
    },
    ProducerField {
        ty: "Inst",
        field: "Load",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Store",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Alloca",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "HeapAlloc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "GEP",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "PtrData",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "PtrMetadata",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "PtrFromParts",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "AtomicLoad",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "AtomicStore",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "AtomicRMW",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "CmpXchg",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Fence",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Br",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "LOWERED: a successor edge, with edge-keyed block arguments (round 1). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "CondBr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED: two successor edges, each with its own edge-keyed arguments and path condition. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Switch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED: successor edges; duplicate cases are a PATH-LOCAL contradiction and decline (round 3). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Call",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED by `lower_inst` (E9): `callee` must resolve to a function in this module, and the callee's `ensures` is imported only under the guard the contract seam establishes. Its `(block, inst_index)` is also the call SITE a `Precondition` can be anchored at (round 8's MAJOR 1). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "CallIndirect",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "Read ONLY as a call-site target (`SiteTarget::IndirectCall`), so a `site` naming it is adjudicated rather than skipped; `lower_inst` declines it. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Return",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/mod.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "LOWERED by `lower_inst`; the returned sort must match the declared signature. `native_discharge/mod.rs` (`site_is_the_only_return`) only COUNTS and locates the `Return`s, to bind a requested postcondition's site; it reads no operand. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "ExtractField",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "InsertField",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "ExtractElement",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "InsertElement",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Const",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "LOWERED by `lower_inst`; an out-of-width constant is a PATH-LOCAL contradiction and declines (round 3). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "NullPtr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "GlobalAddr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Undef",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Assume",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "LOWERED by `lower_inst` as a PRODUCER CLAIM (E15) — recorded as an assumption premise, never silently folded. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Assert",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Walked for operands (its condition, the kind's message operands and a run-time panic location, through trust-ir's own `AssertKind::operands` and `PanicSite::location_value`, for the use-before-definition check only); `lower_inst` has no arm for it, so it reaches the catch-all and DECLINES. `trust_ir_body/check.rs` admits only a site-less assert whose kind carries no operands (`AssertKind::operand_count`, read with `AssertKind::keyword` for the refusal message): the kind names which panic a failure is and never whether the check fails, so the admitted reading is the kindless one; a sited assert or an operand-carrying kind (`bounds_check`, `misaligned_ptr`) is REFUSED by name. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Unreachable",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Copy",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "LOWERED by `lower_inst`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Select",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "LOWERED by `lower_inst`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "SeqMapAddK",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "SeqMapNot",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "SeqMap",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Borrow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "BorrowMut",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "EndBorrow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Retain",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Release",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "IsUnique",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Dealloc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "OpenFrame",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "BindSlot",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "LoadSlot",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "CloseFrame",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "CoroSuspend",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Invoke",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED in a body: `lower_inst`'s catch-all refuses it. `native_discharge/body.rs` reads its `callee` in `direct_callee` only, so that a precondition anchored at it is the callee's and the recursion walk follows it; neither can license a fact. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "LandingPad",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Resume",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "Drop",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. A drop runs the dropped type's destructor, which may free memory or run user code, so reading it as a no-op would decide a different program. `native_discharge/body.rs` names it in `inst_name` for the decline message; `lower_inst`'s catch-all refuses it. A drop is a call of its type's glue, so `direct_callee` reads its `ty` as the key of `Module::drop_glue_for`, for call attribution and the recursion walk only. `trust_ir_body/check.rs` refuses it by name in the advisory lane, and a `#[cfg(test)]` fixture pins that refusal.",
    },
    ProducerField {
        ty: "Inst",
        field: "DialectOp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Named by `inst_name` for the decline message only; `lower_inst`'s catch-all refuses any instruction it does not model, so no field of this variant is ever read. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Inst",
        field: "MemCopy",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. `trust_ir_body/check.rs` refuses it by name (bulk memory is a memory effect the advisory lane does not model); `inst_name` names it for the refusal. The native lane's catch-all declines it. Its presence also means the module has no wire identity at this pin, which both entries refuse before hashing (`wire_identity_gap`).",
    },
    ProducerField {
        ty: "Inst",
        field: "MemSet",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Refused by name in `trust_ir_body/check.rs` and declined by the native lane's catch-all; no wire identity at this pin, refused before hashing.",
    },
    ProducerField {
        ty: "Inst",
        field: "MakeClosure",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. Both body lanes refuse runtime closure construction by name and location, including an unused result. The native lane declares no closure value before declining. Neither the target nor ordered captures license a scalar definition, obligation discharge or lowering witness.",
    },
    ProducerField {
        ty: "Inst",
        field: "MakeAggregate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED. Listed in `trust_ir_body/check.rs`'s exhaustive refusal arm and named by `inst_name`; the native lane's catch-all declines it. No wire identity at this pin, refused before hashing.",
    },
    ProducerField {
        ty: "Inst",
        field: "ArraySplat",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v50's uniform array `[value; n]` (wire Inst tag 59): `n` copies of one register value build an array, and neither lane has an array sort. `native_discharge/body.rs` declines it by name in its own `lower_inst` arm, names it in `inst_name`, and gives it an explicit `result_ty` arm that declares no value. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`. `#[cfg(test)]` fixtures in both files pin the decline and refusal at two, at 2^40 and at `u64::MAX` copies. No field of it is read, so neither lane's answer depends on the length: the decline is constant-size in `n`.",
    },
    ProducerField {
        ty: "Inst",
        field: "AssertInvoke",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. A sited check whose failure enters a landing pad (a terminator with `Invoke`'s successors). `native_discharge/body.rs` names it in `inst_name` for the decline message only; `lower_inst`'s catch-all refuses it. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`. No field of it is read.",
    },
    ProducerField {
        ty: "Inst",
        field: "CallCannotUnwind",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. A direct call with a no-crossing unwind boundary. `lower_inst`'s catch-all refuses it in a body and `inst_name` names it. `native_discharge/body.rs` reads its `callee` in `direct_callee` only, exactly as a `Call`'s, so that a precondition anchored at it is the callee's and the recursion walk follows it; neither can license a fact. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`.",
    },
    ProducerField {
        ty: "Inst",
        field: "CallIndirectCannotUnwind",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. An indirect call with a no-crossing unwind boundary. `lower_inst`'s catch-all refuses it in a body and `inst_name` names it. `call_target_at` matches it by name as an indirect call, so a row anchored at it is adjudicated, never excluded. No field of it is read. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`.",
    },
    ProducerField {
        ty: "Inst",
        field: "DropInvoke",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. `Drop`'s unwinding twin (a terminator). `lower_inst`'s catch-all refuses it in a body and `inst_name` names it. `direct_callee` reads its `ty` as the key of `Module::drop_glue_for`, exactly as a `Drop`'s, for call attribution and the recursion walk only. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`.",
    },
    ProducerField {
        ty: "Inst",
        field: "InvokeIndirect",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. `CallIndirect`'s unwinding twin (a terminator). `lower_inst`'s catch-all refuses it in a body and `inst_name` names it. `call_target_at` matches it by name as an indirect call, so a row anchored at it is adjudicated, never excluded. No field of it is read. `trust_ir_body/check.rs` lists it in the advisory lane's exhaustive outside-v0 refusal arm and names it in `inst_name`.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorContract",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v67's tensor contraction over `Ty::Tensor` values. `native_discharge/body.rs` names it in `inst_name`, and `lower_inst`'s catch-all declines it under that name; `result_ty` and `operand_values` fall through to their empty arms, so no operand or result enters the relation. `trust_ir_body/check.rs` refuses it BY NAME in the advisory lane's tensor arm, before any operand is read, and names it in `inst_name`. No field of it is read. `#[cfg(test)]` fixtures in both files parse it from trust-ir's own text grammar and pin the named refusal.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorMap",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v68's elementwise map over `Ty::Tensor` values; its node list is never walked. Declined and refused BY NAME exactly as `TensorContract`, in both lanes, with the same `#[cfg(test)]` fixtures. No field of it is read.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorReduce",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v68's reduction of a `Ty::Tensor` value; its operator, axes and order are never read. Declined and refused BY NAME exactly as `TensorContract`, in both lanes, with the same `#[cfg(test)]` fixtures.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorView",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v68's affine view of a `Ty::Tensor` value; its index expressions, shape, index and fill are never read. Declined and refused BY NAME exactly as `TensorContract`, in both lanes, with the same `#[cfg(test)]` fixtures.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorGather",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v69's gather from a `Ty::Tensor` value; its coordinates are never read. Declined and refused BY NAME exactly as `TensorContract`, in both lanes, with the same `#[cfg(test)]` fixtures.",
    },
    ProducerField {
        ty: "Inst",
        field: "TensorScatter",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v69's scatter into a `Ty::Tensor` value; its operands and coordinates are never read. Declined and refused BY NAME exactly as `TensorContract`, in both lanes, with the same `#[cfg(test)]` fixtures.",
    },
    // --- Ty --------------------------------------------------------------
    ProducerField {
        ty: "Ty",
        field: "I8",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "I16",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "I32",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "I64",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "I128",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "U8",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "U16",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "U32",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "U64",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "U128",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "Isize",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Usize",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Char",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Error",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "F16",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "F32",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "F64",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Bool",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "Vector",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "StorageLayout",
        field: "size_bytes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Only constructed in a scalar-decoder refusal control; no storage geometry is consumed by either discharge lane. Storage declines before any value lowering.",
    },
    ProducerField {
        ty: "StorageLayout",
        field: "align_bytes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Only constructed in a scalar-decoder refusal control; no storage geometry is consumed by either discharge lane. Storage declines before any value lowering.",
    },
    ProducerField {
        ty: "Ty",
        field: "FnItem",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "A test-only negative verifies that nominal function items remain outside the modeled scalar types. Neither function identity nor zero storage is interpreted as a pointer or integer.",
    },
    ProducerField {
        ty: "Ty",
        field: "Storage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "NOT MODELLED. Geometry-only possibly-uninitialized storage has no scalar value sort. TypeDecoder::sort declines before lowering any value; variant_name names the refusal without reading size or alignment. Neither layout nor byte validity is inferred.",
    },
    ProducerField {
        ty: "Ty",
        field: "Tensor",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v67's tensor `Tensor(elem, rank)`, a run-time collection with no scalar sort. `TypeDecoder::sort` (`native_discharge/ty.rs`) declines it before any value is lowered and `variant_name` names it, reading neither the element nor the rank. `trust_ir_body/check.rs` refuses it through `ScalarTy::from_ty`, which admits a fixed list of scalars, as `UnsupportedType` spelled `tensor<..>`. `#[cfg(test)]` fixtures pin each refusal: `trust_ir_body/check.rs` (`a_tensor_type_is_refused_wherever_it_appears`) at an entry parameter, a return and the type of a `Const`; `native_discharge/body.rs` at an entry parameter and a return (`a_tensor_type_declines_at_a_parameter_and_a_return`) and at a `Const` (`a_tensor_blob_constant_declines_naming_itself`); `native_discharge/ty.rs` at `TypeDecoder::sort` directly, ranks 2 and 0.",
    },
    ProducerField {
        ty: "Ty",
        field: "Ptr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. The `trust_ir_body/check.rs` BoxDeref refusal fixture constructs this pointer type with both present and missing evidence; the instruction is refused before scalar interpretation. Neither pointer validity nor proof authority is inferred.",
    },
    ProducerField {
        ty: "Ty",
        field: "FatPtr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Unit",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Never",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Struct",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Array",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs", "trust_ir_body/check.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. `native_discharge/body.rs` and `trust_ir_body/check.rs` construct it only in `#[cfg(test)]` fixtures, as the type of trust-ir v50's uniform array, whose decline and refusal they pin at two, at 2^40 and at `u64::MAX` elements; neither reads the length.",
    },
    ProducerField {
        ty: "Ty",
        field: "Tuple",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Ty",
        field: "Enum",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Func",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Ref",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "RefMut",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "PtrConst",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "PtrMut",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Rc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Set",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Sequence",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Record",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Closure",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Refine",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Dialect",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/ty.rs"],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which matches `Ty` exhaustively: a type it does not accept DECLINES before any value is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Handle",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Decided by `TypeDecoder::sort` (`native_discharge/ty.rs`), which does not accept it, so a value of this type DECLINES before it is lowered.",
    },
    ProducerField {
        ty: "Ty",
        field: "Ext",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "UNINHABITED here. The extension variant carries trust-ir's level extension, and a module is level R, whose extension `NoExt` has no value; only a template (level S) inhabits it, and no template crosses into this crate.",
    },
    // --- Constant --------------------------------------------------------
    ProducerField {
        ty: "Constant",
        field: "Int",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Constant",
        field: "U128",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Constant",
        field: "Bytes",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Float",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Bool",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "Constant",
        field: "Aggregate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/replay.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `trust_ir_body/check.rs` builds a `#[cfg(test)]` fixture with it, to show an aggregate holding `Constant::Uninit` is refused.",
    },
    ProducerField {
        ty: "Constant",
        field: "Array",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Vector",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Sequence",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Set",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Record",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Closure",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "FnDef",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "SymbolAddr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "PhantomData",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Decided by the constant lowering in `native_discharge/body.rs`, which matches `Constant` exhaustively; a constant it does not model declines.",
    },
    ProducerField {
        ty: "Constant",
        field: "Uninit",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. An unwritten aggregate lane is not a value. `native_discharge/body.rs` names it only in `constant_name`, for the decline message: the constant lowering models `Bool` and `Int` and declines every other constant. `trust_ir_body/check.rs` names it only in a `#[cfg(test)]` fixture that pins the advisory lane's refusal of it.",
    },
    ProducerField {
        ty: "Constant",
        field: "Splat",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v50's uniform array constant `[elem; len]` (wire Constant tag 16). At its only legal type, an array, `TypeDecoder::sort` declines before the value is read. At a scalar sort, `native_discharge/body.rs`'s constant lowering declines it by name in its own arm, and names it in `constant_name`. `trust_ir_body/check.rs`'s `Const` arm refuses it as ill-typed at a scalar type, by name (the array type is refused before the value is read). `#[cfg(test)]` fixtures in both files pin both refusals at two, at 2^40 and at `u64::MAX` copies. Neither `elem` nor `len` is read.",
    },
    ProducerField {
        ty: "Constant",
        field: "FnItem",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Nominal function-item constants have no modeled scalar carrier; default constant refusal remains. The exhaustive producer inventory records the upstream spelling without adding semantics.",
    },
    ProducerField {
        ty: "Constant",
        field: "TensorBlob",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "NOT MODELLED. trust-ir v70's weight constant: a digest into `Module.blobs` and the tensor's extents. At its only legal type, an integer `Ty::Tensor`, the type is refused before the value is read, in both lanes. At a scalar sort, `native_discharge/body.rs`'s constant lowering declines it through its catch-all, named by `constant_name`, and `trust_ir_body/check.rs`'s `Const` arm refuses it as ill-typed, by name. Neither the digest, the extents nor the blob table is read, and a module carrying any blob is refused before this arm in both lanes. `#[cfg(test)]` fixtures in both files pin each refusal against an integer twin.",
    },
    ProducerField {
        ty: "Constant",
        field: "Ext",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "UNINHABITED here. The extension variant carries trust-ir's level extension, and a module is level R, whose extension `NoExt` has no value; only a template (level S) inhabits it, and no template crosses into this crate.",
    },
    // --- ProofEvidence ---------------------------------------------------
    ProducerField {
        ty: "ProofEvidence",
        field: "SmtProof",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The evidence class this lane MINTS and imports; classified onto the evidence row as `TrustVcNativeTrustIrEvidenceKind::SmtProof`. The bytes are opaque here — round 6's invariant: opaque evidence is not proof authority.",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "LeanProof",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified onto the evidence row only. The payload is opaque to this lane and licenses nothing (round 6).",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "KaniHarness",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified onto the evidence row only. The payload is opaque to this lane and licenses nothing (round 6).",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "GammaCrownBound",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified onto the evidence row only. The payload is opaque to this lane and licenses nothing (round 6).",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "TranslationValidation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified onto the evidence row only. The payload is opaque to this lane and licenses nothing (round 6).",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "Trusted",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified and then REFUSED for release admission (`CertificateUsesTrustedEvidence`); a trusted payload is never a discharge.",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "InheritedFromCallee",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Classified onto the evidence row only. The payload is opaque to this lane and licenses nothing (round 6).",
    },
    ProducerField {
        ty: "ProofEvidence",
        field: "CleanCic",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE KERNEL-RECHECK GUARD (rounds 5/7). `term` and `lineage` are read: a callee `ensures` is imported only when the producer's own certificate is CleanCic, lineage-bound and kernel-rechecked, and a failed recheck refuses the bundle.",
    },
    // --- NativeVerificationBundleError -----------------------------------
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnsupportedSchemaVersion",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnsupportedSerializationSchemaVersion",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmptyRequests",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmptyDigest",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "NonCryptographicDigest",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustIrModuleDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustIrModuleHasNoWireIdentity",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "RustReferenceAsPermissionBorrow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "BundlePrimaryLanguageUncovered",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "BundleLanguageUncovered",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "BundleImportLanguageUncovered",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmptyProvenanceField",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidToolIdentityField",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InputDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "NonCanonicalSerialization",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidBundleDiagnosticsPolicy",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidDiagnosticsPolicy",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "VerifierSuiteMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ExpectedVerifierIdentityMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "SourceDigestNotInLineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustIrDigestNotInLineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "Lineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateRequestId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmptyRequestObligations",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateRequestObligation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownRequestObligation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmptyLineageRoots",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateRequestLineageRoot",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownLineageRoot",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "RequestLineageRootTargetMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "RequestSourceDigestNotInLineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "RequestObligationNotInLineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "RequestObligationFunctionMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "CertificateDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "CertificateObligationNotRequested",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateRequestCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "CertificateNotInLineage",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "CertificateVerifierSuiteMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingTrustVcEvidenceForObligation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "THE ONE UPSTREAM REFUSAL THIS LANE REINTERPRETS, and the only variant it destructures. A DISCHARGE request is allowed to lack the evidence bundle it will PRODUCE; `is_discharge_mode_certificate_rule` reads `request` and `obligation` off this variant and carries the refusal past for that request only. Keyed on the variant so a schema that stops emitting it needs no further change here.",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustedCertificateRejected",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustVcCertificateNotDischarged",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingReplayIdentity",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingReplayTranscriptDigest",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidReplayIdentity",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ReplayIdentityVerifierSuiteMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateReplayAtomId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidReplayAtom",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ReplayAtomDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ReplayAtomObligationNotRequested",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ReplayAtomAssertionMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ReplayAtomSourceSpanMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnsupportedNativeRequestMode",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingTrustWpStrongestPostconditionContext",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidTrustMcBmcOptions",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidTrustMcChcOptions",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidTrustWpOptions",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateModuleObligationId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateCompilerFactId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateMonomorphizationId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidCompilerFact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownCompilerFactFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownCompilerFactObligation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidPublicObligationId",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicatePublicObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownObligationSourceFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingEmbeddedObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingEmbeddedPublicObligationIdentity",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidEmbeddedObligationSource",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmbeddedPublicObligationIdMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EmbeddedObligationSourceSpanMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSourceSpan",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSourceAssertion",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownMonomorphization",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "UnknownCompilerFactReference",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSourceCastFact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSourcePointerOffsetFact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingObligationSourceTraitObjectMetadataFact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ObligationSourceFactMonomorphizationMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ObligationSourceFactFunctionMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "ObligationSourceFactObligationMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateEvidenceBundle",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceRequestUnknown",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceRequestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceTrustIrModuleDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceRequestDigestMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceProvenanceMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceObligationMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingEvidenceArtifacts",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "DuplicateEvidenceArtifact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "InvalidEvidenceArtifact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "EvidenceArtifactSuiteMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Every upstream refusal except the one below is FATAL here: the bundle is refused, not reasoned about (round 4's input gate).",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "MissingTrustVcDischargeFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Upstream's mode-aware discharge-request rule; like every upstream refusal but the one relaxed above, it is FATAL here.",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustVcDischargeRequestCarriesCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Upstream's mode-aware discharge-request rule; like every upstream refusal but the one relaxed above, it is FATAL here.",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustVcDischargeObligationNotSitedInFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Upstream's mode-aware discharge-request rule; like every upstream refusal but the one relaxed above, it is FATAL here.",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "TrustVcObligationBothImportedAndDischarged",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Upstream's mode-aware discharge-request rule; like every upstream refusal but the one relaxed above, it is FATAL here.",
    },
    ProducerField {
        ty: "NativeVerificationBundleError",
        field: "FormulaTextsDisagree",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Rendered into the refusal text only. Upstream refuses an obligation whose smtlib2 payload and smtlib rendering differ; like every upstream refusal but the one relaxed above, it is FATAL here.",
    },
    // --- NativeCompilerFactRef -------------------------------------------
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "AdtLayout",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "FatPointer",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "TraitObjectMetadata",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "PointerOffset",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "Cast",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    ProducerField {
        ty: "NativeCompilerFactRef",
        field: "Monomorphization",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The typed compiler-fact reference an obligation source carries. Classified onto the artifact binding as `TrustVcNativeCompilerFactKind`; the FACT ITSELF is never consulted as a premise.",
    },
    // --- NativeAdapterInput ----------------------------------------------
    ProducerField {
        ty: "NativeAdapterInput",
        field: "RustMir",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's statement of what it lowered FROM. Identity only; it licenses nothing in the lane.",
    },
    ProducerField {
        ty: "NativeAdapterInput",
        field: "RustThir",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's THIR source digest is retained as distinct input identity. It is never relabelled as a MIR body and grants no source refinement or proof authority.",
    },
    ProducerField {
        ty: "NativeAdapterInput",
        field: "TrustIrModule",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's statement of what it lowered FROM. Identity only; it licenses nothing in the lane.",
    },
    // --- NativeVerificationRequest ---------------------------------------
    ProducerField {
        ty: "NativeVerificationRequest",
        field: "TrustVc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "Which verifier a request addresses. Only the `TrustVc` arm is consumed here; the others are skipped, not reasoned about. `native_assertion_id.rs` matches it to read each TrustVc request's replay atoms in the input gate; only TrustVc requests are read there.",
    },
    ProducerField {
        ty: "NativeVerificationRequest",
        field: "TrustMc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Which verifier a request addresses. Only the `TrustVc` arm is consumed here; the others are skipped by a wildcard and never named, so no TrustMc request field is read.",
    },
    ProducerField {
        ty: "NativeVerificationRequest",
        field: "TrustWp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs"],
        note: "Which verifier a request addresses. Only the `TrustVc` arm is consumed here; the others are skipped by a wildcard, so the lane reads no TrustWp request field. `native_assertion_id.rs` names it only in a unit test, to show that a TrustWp request's atom licenses nothing.",
    },
    // --- ObligationKind --------------------------------------------------
    ProducerField {
        ty: "ObligationKind",
        field: "Precondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "Postcondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_coverage/tests.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam. `native_coverage/tests.rs` builds a rule-5 fixture obligation with it.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "LoopInvariant",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "TypeInvariant",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "RefinementType",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "TranslationValidation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "MemorySafety",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "PanicFreedom",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "TemporalSafety",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "Liveness",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "ArithmeticSafety",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `obligation_kind` in `native_trust_ir_bundle.rs` files it as `PanicFreedom` on an evidence row, which trust-ir defines as routing identically; a label only.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "BoundsCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `obligation_kind` in `native_trust_ir_bundle.rs` files it as `PanicFreedom` on an evidence row, which trust-ir defines as routing identically; a label only.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "GiveBackRefinement",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "THE DECISION-BEARING KIND. It selects the def-site `requires` a callee contract may be built from and dispatches every arm of `callee_contract_facts`; the compiler-fact `cause` is a SECOND rendering of it and is cross-checked at the export seam. `obligation_kind` in `native_trust_ir_bundle.rs` maps it to `None`, so an imported or produced certificate for it is refused by name.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "Termination",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "No faithful native label: `obligation_kind` in `native_trust_ir_bundle.rs` maps it to `None`, and an imported or produced certificate for such an obligation is refused by name (`NativeTrustIrImportObligationKindUnrepresentable`). Never filed as another kind.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "Ownership",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "No faithful native label: `obligation_kind` in `native_trust_ir_bundle.rs` maps it to `None`, and an imported or produced certificate for such an obligation is refused by name (`NativeTrustIrImportObligationKindUnrepresentable`). Never filed as another kind.",
    },
    ProducerField {
        ty: "ObligationKind",
        field: "Custom",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "No faithful native label: `obligation_kind` in `native_trust_ir_bundle.rs` maps it to `None`, and an imported or produced certificate for such an obligation is refused by name (`NativeTrustIrImportObligationKindUnrepresentable`). Never filed as another kind.",
    },
    // --- ClauseSort ------------------------------------------------------
    //
    // The sort of one of a clause's free names (`ProofFormula::bindings`).
    // `native_coverage.rs` (coverage rule 5) reads it ONLY to spell the name's
    // variable type for trust-ir's own reader (`surface_type`), which then
    // reads the payload over the clause's bindings. Rule 5 is a REFUSAL gate:
    // a sort can make a payload READ, never admit a certificate — admission
    // still needs basis K, a kernel replay of that very certificate. A sort
    // the surface cannot type leaves the name out, so a use of it is refused.
    ProducerField {
        ty: "ClauseSort",
        field: "Bool",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: spelled `Bool` for trust-ir's reader; the payload is then read over a Bool-typed name. Refusal gate only.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "Int",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: spelled `Int` for trust-ir's reader (the nonneg clause's sort). Refusal gate only.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "BitVec",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: spelled `BitVec(<width>)` for trust-ir's reader, which refuses a zero width. Refusal gate only.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "Array",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: no Linked-surface type, so the name is left out of the environment and any use of it is refused as undeclared.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "Float",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: no Linked-surface type; the name is left out and any use of it refused.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "RoundingMode",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: no Linked-surface type; the name is left out and any use of it refused.",
    },
    ProducerField {
        ty: "ClauseSort",
        field: "Datatype",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs"],
        note: "Coverage rule 5: no Linked-surface type; the name is left out and any use of it refused.",
    },
    // --- ProofStatus -----------------------------------------------------
    ProducerField {
        ty: "ProofStatus",
        field: "Pending",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "The producer's status label. Round 6's invariant: a status label is not proof authority — `Discharged`/`Trusted` are never taken as a proof, and an undecided status is not an error. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofStatus",
        field: "Discharged",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The producer's status label. Round 6's invariant: a status label is not proof authority — `Discharged`/`Trusted` are never taken as a proof, and an undecided status is not an error. `native_coverage/tests.rs` builds a rule-5 fixture obligation with it; the status is not read by the coverage rule.",
    },
    ProducerField {
        ty: "ProofStatus",
        field: "Failed",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The producer's status label. Round 6's invariant: a status label is not proof authority — `Discharged`/`Trusted` are never taken as a proof, and an undecided status is not an error.",
    },
    ProducerField {
        ty: "ProofStatus",
        field: "Trusted",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The producer's status label. Round 6's invariant: a status label is not proof authority — `Discharged`/`Trusted` are never taken as a proof, and an undecided status is not an error.",
    },
    ProducerField {
        ty: "ProofStatus",
        field: "Certified",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The producer's status label. Round 6's invariant: a status label is not proof authority — `Discharged`/`Trusted` are never taken as a proof, and an undecided status is not an error.",
    },
    // --- NativeObligationCause -------------------------------------------
    ProducerField {
        ty: "NativeObligationCause",
        field: "Precondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Postcondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Assert",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "BoundsCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "OverflowCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "LayoutCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "CastCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "PointerOffset",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "BorrowCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Translation",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Panic",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Temporal",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    ProducerField {
        ty: "NativeObligationCause",
        field: "Other",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The compiler-fact rendering of the obligation KIND. Republished on the binding and folded into `obligation_source_digest`, and cross-checked against `ObligationKind` at the export seam.",
    },
    // --- TrustVcVerificationMode -----------------------------------------
    ProducerField {
        ty: "TrustVcVerificationMode",
        field: "ImportProofCertificates",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Selects the lane (import / merge / discharge). The verdict/mode pairing is enforced where the verdict is minted.",
    },
    ProducerField {
        ty: "TrustVcVerificationMode",
        field: "MergeProofCertificates",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Selects the lane (import / merge / discharge). The verdict/mode pairing is enforced where the verdict is minted.",
    },
    ProducerField {
        ty: "TrustVcVerificationMode",
        field: "DischargeProofObligations",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Selects the lane (import / merge / discharge). The verdict/mode pairing is enforced where the verdict is minted.",
    },
    // --- NativeVerifierSuite ---------------------------------------------
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "Unknown",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "TrustVc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "TrustMc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "TrustWp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "AY",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "TRust",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "TrustIr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    ProducerField {
        ty: "NativeVerifierSuite",
        field: "Other",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which suite the producer addressed. Identity, checked against this crate's own suite identity; licenses nothing.",
    },
    // --- NativeEvidenceArtifactKind --------------------------------------
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustVcCertificateImport",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustVcMergedCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustMcHornClauses",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustMcPdrTrace",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustMcModel",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustWpVerificationCondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustWpReplayTrace",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "TrustWpAbducedPrecondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "ReplayTranscript",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "Other",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "Btor2Trace",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "Btor2Proof",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "NativeCompiledArtifact",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    ProducerField {
        ty: "NativeEvidenceArtifactKind",
        field: "BackendCapabilityMetadata",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The evidence-bundle artifact class. Identity only.",
    },
    // --- NativeBundleProducer --------------------------------------------
    ProducerField {
        ty: "NativeBundleProducer",
        field: "TRust",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which compiler produced the bundle. Identity only — NO derivation is enforced from it (see `native_assertion_id`'s module docs on `stable_u32_id`).",
    },
    ProducerField {
        ty: "NativeBundleProducer",
        field: "TSwift",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which compiler produced the bundle. Identity only — NO derivation is enforced from it (see `native_assertion_id`'s module docs on `stable_u32_id`).",
    },
    ProducerField {
        ty: "NativeBundleProducer",
        field: "TC",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which compiler produced the bundle. Identity only — NO derivation is enforced from it (see `native_assertion_id`'s module docs on `stable_u32_id`).",
    },
    ProducerField {
        ty: "NativeBundleProducer",
        field: "TrustIr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which compiler produced the bundle. Identity only — NO derivation is enforced from it (see `native_assertion_id`'s module docs on `stable_u32_id`).",
    },
    ProducerField {
        ty: "NativeBundleProducer",
        field: "Clean",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Which compiler produced the bundle. Identity only — NO derivation is enforced from it (see `native_assertion_id`'s module docs on `stable_u32_id`).",
    },
    // --- CallingConv -----------------------------------------------------
    ProducerField {
        ty: "CallingConv",
        field: "C",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Fast",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Cold",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Rust",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Swift",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "CUnwind",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "SysV64",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Win64",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "Aapcs",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "EfiApi",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "VectorCall",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    ProducerField {
        ty: "CallingConv",
        field: "RustCold",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Declared calling convention. NOT a premise; the lane models no ABI.",
    },
    // --- Endianness ------------------------------------------------------
    ProducerField {
        ty: "Endianness",
        field: "Little",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs"],
        note: "Target endianness (E16).",
    },
    ProducerField {
        ty: "Endianness",
        field: "Big",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Target endianness (E16).",
    },
    // --- StructPassingPolicy ---------------------------------------------
    ProducerField {
        ty: "StructPassingPolicy",
        field: "NativeC",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "native_discharge/ty.rs"],
        note: "Target struct-passing policy. Every aggregate declines before this matters.",
    },
    ProducerField {
        ty: "StructPassingPolicy",
        field: "AlwaysMemory",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Target struct-passing policy. Every aggregate declines before this matters.",
    },
    ProducerField {
        ty: "StructPassingPolicy",
        field: "Unclassified",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Target struct-passing policy. Every aggregate declines before this matters.",
    },
    // --- BinOp -----------------------------------------------------------
    ProducerField {
        ty: "BinOp",
        field: "Add",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "BinOp",
        field: "Sub",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "BinOp",
        field: "Mul",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "BinOp",
        field: "UDiv",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "SDiv",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "URem",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "SRem",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FAdd",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FSub",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FMul",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FDiv",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FRem",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FMin",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FMax",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "And",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "Or",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "Xor",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "Shl",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "LShr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "AShr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "BAnd",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "BOr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "BXor",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The arithmetic/logical operation `Inst::BinOp` names; modelled per operation, and an operation this lane cannot model at the declared width declines. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name.",
    },
    ProducerField {
        ty: "BinOp",
        field: "RotL",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED by the native lane, whose catch-all declines it. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name. It also has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    ProducerField {
        ty: "BinOp",
        field: "RotR",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED by the native lane, whose catch-all declines it. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name. It also has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    ProducerField {
        ty: "BinOp",
        field: "FCopySign",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT MODELLED by the native lane, whose catch-all declines it. `trust_ir_body/check.rs` names it in `arith_kind`, the advisory lane's exhaustive operator classification, which maps it to no arithmetic, so a body using it is refused `NotAnswerable` by name. It also has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    // --- UnOp ------------------------------------------------------------
    ProducerField {
        ty: "UnOp",
        field: "Neg",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FNeg",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FAbs",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FSqrt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FFloor",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FCeil",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "FTrunc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "Not",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "CtPop",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names.",
    },
    ProducerField {
        ty: "UnOp",
        field: "CtLz",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names. NOT MODELLED by either lane; it has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    ProducerField {
        ty: "UnOp",
        field: "CtTz",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names. NOT MODELLED by either lane; it has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    ProducerField {
        ty: "UnOp",
        field: "BSwap",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names. NOT MODELLED by either lane; it has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    ProducerField {
        ty: "UnOp",
        field: "BitReverse",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The unary operation `Inst::UnOp` names. NOT MODELLED by either lane; it has no wire identity at this pin, so a module using it is refused before hashing.",
    },
    // --- ICmpOp ----------------------------------------------------------
    ProducerField {
        ty: "ICmpOp",
        field: "Eq",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Ne",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Ult",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Ule",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Ugt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Uge",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Slt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Sle",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Sgt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ICmpOp",
        field: "Sge",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/lower.rs"],
        note: "The integer comparison `Inst::ICmp` names; signedness is modelled, not assumed. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    // --- OverflowOp ------------------------------------------------------
    ProducerField {
        ty: "OverflowOp",
        field: "AddOverflow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "The checked operation `Inst::Overflow` names. `Inst::Overflow` is not modelled, so no arm reads it. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "OverflowOp",
        field: "SubOverflow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs"],
        note: "The checked operation `Inst::Overflow` names. `Inst::Overflow` is not modelled, so no arm reads it. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "OverflowOp",
        field: "MulOverflow",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/check.rs", "trust_ir_body/lower.rs"],
        note: "The checked operation `Inst::Overflow` names. `Inst::Overflow` is not modelled, so no arm reads it. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    // --- CastOp ----------------------------------------------------------
    ProducerField {
        ty: "CastOp",
        field: "Trunc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "ZExt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "SExt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPTrunc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPExt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPToUI",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPToSI",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "UIToFP",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "SIToFP",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "PtrToInt",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "IntToPtr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "PtrToPtr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "Bitcast",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "Transmute",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "ReifyFnPointer",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPToSISat",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "CastOp",
        field: "FPToUISat",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "The cast `Inst::Cast` names. Round 2: modelled faithfully per op, and an op the lane cannot model declines rather than being approximated.",
    },
    ProducerField {
        ty: "ClosureTy",
        field: "func",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. Only a valid test fixture constructs the apparent signature reference. Both body lanes refuse MakeClosure before the target or captures can establish a relation or discharge.",
    },
    ProducerField {
        ty: "ClosureTy",
        field: "captures",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs"],
        note: "NOT READ. Only a valid test fixture constructs capture types. Ordered live captures are outside both body lanes and grant no proof authority. The lib.rs union site is a same-name field in TrustScalarCastVerification, not ClosureTy captures. It returns bounded encoder observations separately from the unchanged native report and grants no proof authority.",
    },
    // --- FuncTy ----------------------------------------------------------
    ProducerField {
        ty: "FuncTy",
        field: "params",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_discharge/body.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/replay.rs"],
        note: "E23: the declared parameter sorts, and the only source of a parameter's sort. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "FuncTy",
        field: "returns",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/body.rs", "trust_ir_body/check.rs"],
        note: "E23: the declared return sorts; a `Return` whose value disagrees declines. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "FuncTy",
        field: "is_vararg",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/check.rs"],
        note: "NOT READ. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "FuncTy",
        field: "abi",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. The typed signature ABI (trust-ir v60: each parameter's and return's checked source ABI placement). Neither lane models a calling convention or a register/stack placement: the native lane's sorts come from `params` / `returns` alone, and the advisory body lane's replay rebuilds its entry signature with no ABI. The descriptor is checked by trust-ir itself (the binary reader and `validate_module`, the P1 input gate), and the advisory digest in `trust_ir_body/binding.rs` keeps the `func_types` table, so a changed descriptor moves that digest.",
    },
    // --- SwitchCase ------------------------------------------------------
    ProducerField {
        ty: "SwitchCase",
        field: "value",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs", "trust_ir_body/replay.rs"],
        note: "The case constant. Duplicate case values are a PATH-LOCAL contradiction and decline (round 3). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "SwitchCase",
        field: "target",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_discharge/body.rs"],
        note: "The successor block of this case edge.",
    },
    ProducerField {
        ty: "SwitchCase",
        field: "args",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_discharge/body.rs"],
        note: "Edge-keyed block arguments for this case edge (round 1).",
    },
    // --- SourceSpan ------------------------------------------------------
    ProducerField {
        ty: "SourceSpan",
        field: "file",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_adapter.rs"],
        note: "Republished on the artifact binding as `TrustVcNativeSourceSpan`; identity only.",
    },
    ProducerField {
        ty: "SourceSpan",
        field: "line",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Republished on the artifact binding; identity only.",
    },
    ProducerField {
        ty: "SourceSpan",
        field: "col",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Republished on the artifact binding; identity only.",
    },
    // --- ProofLineageNode ------------------------------------------------
    ProducerField {
        ty: "ProofLineageNode",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Lineage node identity; walked from the request's roots to find the node that carries a certificate. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used); `trust_ir_body/replay.rs` rebuilds the module and witness for trust-ir's own reference interpreter, whose replay only decides whether an advisory REFUTATION is reported. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "transform",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "source_module",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "target_module",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ.",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "obligations",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_assertion_id.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "NOT READ as a lineage fact; the listed sites are other `obligations` fields (the scan unions by field NAME). MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_assertion_id.rs` reads `TrustVcNativeRequest::obligations` in the replay-atom input gate: an atom citing an obligation its request does not list refuses the bundle.",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "certificates",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Walked to bind a certificate reference to its lineage node, and to refuse a discharge request whose lineage closure already certifies one of its own obligations (it can only refuse).",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "replay",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's replay identity for this node — republished as replay metadata and graded for MissingReplayIdentity / MissingReplayTranscriptDigest. A producer CLAIM about replay, never a replay this crate performed.",
    },
    ProducerField {
        ty: "ProofLineageNode",
        field: "depends_on",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Walked when searching the lineage graph for the node carrying a certificate, and when collecting a discharge request's lineage closure for the refusal above.",
    },
    // --- ProofCertificateRef ---------------------------------------------
    ProducerField {
        ty: "ProofCertificateRef",
        field: "obligation",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "Which obligation the certificate is offered for; matched against the request. `native_coverage.rs` looks up the certificate's obligation for coverage rule 5 and names it in the basis. `native_assertion_id.rs` reads `NativeReplayAtom::obligation` (which obligation an atom renders the identity of; see that row).",
    },
    ProducerField {
        ty: "ProofCertificateRef",
        field: "prover",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "The producer's prover label. Identity only — round 6: a label is not proof authority. `native_coverage.rs` copies it into the established basis; identity only.",
    },
    ProducerField {
        ty: "ProofCertificateRef",
        field: "evidence_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_coverage.rs", "native_coverage/tests.rs", "native_trust_ir_bundle.rs"],
        note: "Republished as the evidence digest and bound into the artifact fingerprint. `native_coverage.rs` copies it into the established basis, which the artifact fingerprint binds.",
    },
    // --- ProofReplayIdentity ---------------------------------------------
    ProducerField {
        ty: "ProofReplayIdentity",
        field: "engine",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Republished as replay metadata; a producer claim.",
    },
    ProducerField {
        ty: "ProofReplayIdentity",
        field: "invocation",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Republished as replay metadata; a producer claim.",
    },
    ProducerField {
        ty: "ProofReplayIdentity",
        field: "transcript_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Republished; its ABSENCE is a fail-closed rejection (MissingReplayTranscriptDigest), its presence licenses nothing.",
    },
    // --- NativeRequestProvenance -----------------------------------------
    ProducerField {
        ty: "NativeRequestProvenance",
        field: "verifier_suite",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's suite claim; checked against this crate's own identity, and republished as the suite identity.",
    },
    ProducerField {
        ty: "NativeRequestProvenance",
        field: "expected_verifier",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's expected-verifier claim; graded into MissingSuiteIdentity.",
    },
    ProducerField {
        ty: "NativeRequestProvenance",
        field: "solvers",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs"],
        note: "The producer's solver identities; graded into MissingSolverIdentity. Never taken as evidence that a solver ran.",
    },
    ProducerField {
        ty: "NativeRequestProvenance",
        field: "replay",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "The producer's replay identity for the request; the fallback source of replay metadata when the lineage node has none.",
    },
    ProducerField {
        ty: "NativeRequestProvenance",
        field: "replay_context",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "THE EXPORT SEAM's rendering E. `native_trust_ir_bundle.rs` hands the CITING request's context to `native_assertion_id.rs`, which reads its `Assertion` atoms: the input gate refuses a bundle whose atom states another formula than its obligation or another id than the compiler fact, and the evidence row publishes an assertion id only when exactly one atom for the obligation states it. The context is covered by the request digest the row republishes. Only TrustVc requests' contexts are read.",
    },
    // --- NativeReplayContext ---------------------------------------------
    ProducerField {
        ty: "NativeReplayContext",
        field: "atoms",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs"],
        note: "Rendering E's carrier: `native_assertion_id.rs` filters the `Assertion` atoms citing one obligation. A refusal gate and a license for the published assertion id; never read as a premise or a proof.",
    },
    ProducerField {
        ty: "NativeReplayContext",
        field: "unsupported_modes",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ. trust-ir's bundle validator refuses every request that carries one (`UnsupportedNativeRequestMode`) before this lane runs.",
    },
    // --- NativeReplayAtom ------------------------------------------------
    ProducerField {
        ty: "NativeReplayAtom",
        field: "id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs", "trust_ir_body/replay.rs"],
        note: "Named in the export seam's refusals (`native_assertion_id.rs`); identity only, licenses nothing.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "kind",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "`native_assertion_id.rs`: only an `Assertion` atom renders its certificate's goal and so may license an id; an `Assumption` atom is a premise and licenses nothing, though its id is still checked against the compiler fact.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "formula",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "`native_assertion_id.rs` compares an `Assertion` atom's WHOLE formula (schema, payload, rendering, sort, bindings) with its obligation's and refuses the bundle when they differ. ROUND 14: `AssertionIdIndex::of` also reads the payload source record of every atom formula, in every request, that is not its cited obligation's own formula: a number it renders publishes no id, and an unreadable one withdraws every id in the bundle. Both reads can only WITHDRAW a license. The atom's formula is never grounded or proved.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "payload_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs"],
        note: "Written only by the export seam's unit tests (recomputed after an edit so trust-ir's own digest check is not what refuses it). trust-ir validates it; this lane never reads it as evidence.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "obligation",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_assertion_id.rs", "native_coverage.rs", "native_discharge/body.rs", "native_trust_ir_bundle.rs"],
        note: "`native_assertion_id.rs`: which obligation an atom renders the identity of. An atom citing none licenses nothing; one citing an obligation the module does not carry, or its request does not list, refuses the bundle.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "assertion_id",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_assertion_id.rs", "native_trust_ir_bundle.rs"],
        note: "Rendering E. `native_assertion_id.rs` refuses the bundle when it differs from the compiler fact's number (rendering A), and publishes A only when exactly one `Assertion` atom for the obligation in the citing request states it; the value is then recorded as the row's `independent_assertion_id`. ROUND 16: `AssertionIdIndex::of` withdraws the number when an atom of any kind, in any request, states it beside a formula that is not its cited obligation's own. That read can only WITHDRAW a license.",
    },
    ProducerField {
        ty: "NativeReplayAtom",
        field: "span",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs"],
        note: "NOT READ by the export seam; trust-ir checks it against the compiler fact's span.",
    },
    // --- NativeReplayAtomKind --------------------------------------------
    ProducerField {
        ty: "NativeReplayAtomKind",
        field: "Assumption",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs"],
        note: "Named only by the export seam's unit tests: an `Assumption` atom licenses no id.",
    },
    ProducerField {
        ty: "NativeReplayAtomKind",
        field: "Assertion",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_assertion_id.rs"],
        note: "The atom kind that renders a certificate's goal and its assertion id (see `NativeReplayAtom::kind`).",
    },
    // --- NativeEvidenceArtifact ------------------------------------------
    ProducerField {
        ty: "NativeEvidenceArtifact",
        field: "name",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/lower.rs"],
        note: "Evidence-bundle artifact name; identity only. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeEvidenceArtifact",
        field: "kind",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_artifact.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/binding.rs", "trust_ir_body/check.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "Evidence-bundle artifact class; identity only. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label; `trust_ir_body/check.rs` is the advisory lane's structural check, which admits or REFUSES by variant (a refusal is `NotAnswerable` naming the instruction); `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeEvidenceArtifact",
        field: "digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Evidence-bundle artifact digest; identity only.",
    },
    // --- NativeToolIdentity ----------------------------------------------
    ProducerField {
        ty: "NativeToolIdentity",
        field: "name",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_assertion_id.rs", "native_discharge/body.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_body/lower.rs"],
        note: "Tool identity republished onto the suite/solver identity; identity only. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "NativeToolIdentity",
        field: "version",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Tool version republished; identity only.",
    },
    ProducerField {
        ty: "NativeToolIdentity",
        field: "revision",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Tool revision republished; identity only.",
    },
    ProducerField {
        ty: "NativeToolIdentity",
        field: "digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Tool digest republished; identity only.",
    },
    // --- TrustVcNativeEvidenceBundle -------------------------------------
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "request",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/mod.rs", "native_scalar_cast.rs", "native_trust_ir_bundle.rs"],
        note: "Which request the release-evidence bundle belongs to. The native_scalar_cast.rs union site retains the same actual typed request inside bounded observation data. It creates no second question, assumes no producer witness, and grants no source/translation/proof-grade authority.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "mode",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_trust_ir_bundle.rs"],
        note: "The bundle's mode; must agree with the request's.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "obligations",
        kind: ProducerFieldKind::StructField,
        read_sites: &["lib.rs", "mir_memory.rs", "native_assertion_id.rs", "native_discharge/mod.rs", "native_trust_ir_bundle.rs", "trust_ir_adapter.rs", "trust_ir_body/lower.rs", "trust_ir_body/mod.rs"],
        note: "The obligations the bundle covers. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/lower.rs` lowers the admitted body into the advisory lane's typed query (plus a `#[cfg(test)]` fixture builder); `trust_ir_body/mod.rs` drives the advisory lane: it locates the cited `Assert` site, scopes the obligation kinds it answers, and reads statuses, certificates, formulas, annotations and `requires` ONLY to set `ignored_inputs` (seen and deliberately not used). The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`). `native_assertion_id.rs` reads `TrustVcNativeRequest::obligations` in the replay-atom input gate: an atom citing an obligation its request does not list refuses the bundle.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "verifier",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ under that name.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "solvers",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs"],
        note: "Solver identities carried by the bundle.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "replay",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "Replay identity carried by the bundle.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "trust_ir_module_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Bound into the artifact; a mismatch is a fail-closed rejection.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "request_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "Bound into the artifact; a mismatch is a fail-closed rejection.",
    },
    ProducerField {
        ty: "TrustVcNativeEvidenceBundle",
        field: "artifacts",
        kind: ProducerFieldKind::StructField,
        read_sites: &[],
        note: "NOT READ under that name.",
    },
    // --- ProofDigest -----------------------------------------------------
    ProducerField {
        ty: "ProofDigest",
        field: "algorithm",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ; the digest is used through its `Display`/accessors, never field by field. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    ProducerField {
        ty: "ProofDigest",
        field: "bytes",
        kind: ProducerFieldKind::StructField,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "NOT READ; see `algorithm`. MERGED 2026-09-23, upstream's ADVISORY body lane: `trust_ir_body/binding.rs` computes the advisory lane's provisional semantic digest, which CLEARS every proof-status, certificate, diagnostic and debug field before hashing the rest, so the digest cannot move with a producer label. The invariant holds there by construction: that lane's answer writes back no `ProofStatus`, mints no `trust_ir::ProofCertificate`, never enters `proof_evidence`, and its verdicts never satisfy `is_ok` (see `TrustVcNativeTrustIrDischargeAnswer`).",
    },
    // --- ValidationError (trust_ir_build) --------------------------------
    //
    // ROUND 11. The producer's own validator verdict. `validate_module` is this
    // lane's P1 INPUT GATE: every error it returns refuses the bundle, so the
    // only rows the census needs are the variants this crate singles out for
    // DIFFERENT treatment — those are the ones that can let something through.
    //
    // `ValidationError` is `#[non_exhaustive]` upstream with about a hundred
    // variants, so the compile-time exhaustive destructure that pins every other
    // producer enum here cannot be written for it. What pins it instead:
    // `every_producer_named_path_this_crate_names_is_tabled` fails on any
    // variant path this crate names without a row, and the variant below is
    // written as a PATTERN, so reshaping or removing it upstream breaks the
    // build.
    ProducerField {
        ty: "ValidationError",
        field: "DischargedWithoutCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_trust_ir_bundle.rs"],
        note: "THE ONE CARVE-OUT. `is_proof_replay_capability_verdict` singles this variant out so an IMPORT of a `Discharged` obligation whose certificate upstream will not replay is graded by this lane rather than refused outright; every other variant refuses the bundle. The carve-out is scoped by `Builder::established_callee_ensures`, which still demands `Certified` plus a lineage-bound `CleanCic`, so nothing is assumed from the label alone.",
    },
    ProducerField {
        ty: "ValidationError",
        field: "CoverageRowExceedsEstablished",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Named only by the `native_coverage` unit tests, which build one as the refusal a coverage report can carry. The code never matches it by name: `judge_certificate` treats EVERY refusal in `coverage_establishment_report` as fatal for the whole bundle, whatever its variant.",
    },
    // --- InterpretErrorCode (MERGED 2026-09-23: upstream's ADVISORY body lane) ---
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedDialectOp",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedCall",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedMemory",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedVectorShape",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedInstruction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedCast",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UnsupportedFloat",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "TypeError",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "UndefinedBehavior",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/replay.rs"],
        note: "Matched by `trust_ir_body/replay.rs` to classify a replay that hits undefined behaviour (the checked-op pack's `Undef`) — which is why the lane decides the HAVOC reading and tags the verdict with it. An interpreter outcome, not a producer claim; the answer it feeds is advisory.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "Panic",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/replay.rs"],
        note: "The reference interpreter's own classification of a witness REPLAY, matched by `trust_ir_body/replay.rs`: a `Panic` at the cited site is what lets an advisory counterexample be reported as `Refuted`. An outcome of RUNNING the body under trust-ir's interpreter, not a producer claim; and the answer it feeds is advisory (never `is_ok`, never a certificate, never a status write-back).",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "OutOfFuel",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "OutOfMemory",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "MissingFunction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "InvalidFunctionPointer",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "SignatureMismatch",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "MissingBlock",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "MissingValue",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "MalformedInstruction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ: `trust_ir_body/replay.rs` matches only `Panic` and `UndefinedBehavior`; every other interpreter error falls through to the lane's generic replay-failure arm, which never reports a refutation.",
    },
    ProducerField {
        ty: "InterpretErrorCode",
        field: "AssumeViolated",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/replay.rs"],
        note: "`trust_ir_body/replay.rs` maps it to `Outcome::AssumeViolated`: the replayed input lies outside the assumed domain. Like undefined behaviour it is decisive for nothing; it never turns an advisory answer into a refutation.",
    },
    // --- ProofDigestAlgorithm (MERGED 2026-09-23: upstream's ADVISORY body lane) ---
    ProducerField {
        ty: "ProofDigestAlgorithm",
        field: "Sha256",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "Matched by `trust_ir_body/binding.rs` to encode, as one tag byte, the algorithm of a digest the lane COMPUTED itself (`Module::stable_digest` over the body with every proof-status, certificate and debug field cleared) into its provisional semantic digest. Not a producer claim, and the digest binds an advisory answer to its body only; it confers no authority.",
    },
    ProducerField {
        ty: "ProofDigestAlgorithm",
        field: "TrustIrStableV1",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["trust_ir_body/binding.rs"],
        note: "Matched by `trust_ir_body/binding.rs` to encode, as one tag byte, the algorithm of a digest the lane COMPUTED itself (`Module::stable_digest` over the body with every proof-status, certificate and debug field cleared) into its provisional semantic digest. Not a producer claim, and the digest binds an advisory answer to its body only; it confers no authority.",
    },
    ProducerField {
        ty: "CoverageAssurance",
        field: "bound",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_discharge/formula.rs"],
        note: "NOT READ as a producer field: release admission never reads the in-module coverage row (see `ProofCertificate::assurance`). The `native_discharge/formula.rs` sites are the formula decoder's own quantifier-binder stack (`self.bound`), a trust-vc field that shares the name.",
    },
    ProducerField {
        ty: "CoverageAssurance",
        field: "request_digest",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_artifact.rs", "native_trust_ir_bundle.rs"],
        note: "The request the recorded bound cites. `native_trust_ir_bundle.rs` matches it against every request's RECOMPUTED `stable_digest`; an unknown citation, or one whose request does not list the obligation, refuses coverage. The field name is shared with trust-vc's own report and artifact types, which account for the other sites.",
    },
    ProducerField {
        ty: "CoverageBound",
        field: "Unbounded",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "The only bound release admission accepts, and only as trust-ir-build's basis-K verdict for this very certificate (`judge_certificate` in `native_coverage.rs`); the in-module row is never read. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "CoverageBound",
        field: "UnwindBounded",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Refused at release grade by the `other` arm of `judge_certificate` (`CertificateCoverageBounded`). Named only by the unit tests in `native_coverage/tests.rs`.",
    },
    ProducerField {
        ty: "CoverageBound",
        field: "ModelBounded",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Refused at release grade by the `other` arm of `judge_certificate` (`CertificateCoverageBounded`). Named only by the unit tests in `native_coverage/tests.rs`.",
    },
    ProducerField {
        ty: "CoverageBound",
        field: "Unrecorded",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Refused at release grade by the `other` arm of `judge_certificate` (`CertificateCoverageBounded`). Named only by the unit tests in `native_coverage/tests.rs`.",
    },
    ProducerField {
        ty: "CertificateCoverage",
        field: "Established",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "One certificate's verdict in the report `coverage_establishment_report` COMPUTES in this process from the Clean-kernel replay of the certificate (basis K); not a producer row. `judge_certificate` accepts it only with an `Unbounded` bound, a `KernelReplayedClaim` basis naming this very certificate and a classified family; anything else rejects. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "CertificateCoverage",
        field: "Undetermined",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "Rejects: `CertificateCoverageBasisNotThisCertificate` for `NotTheReplayedCertificate`, `CertificateCoverageUndetermined` for every other reason. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "CertificateCoverage",
        field: "Refused",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "Rejects (`CertificateCoverageRefused`). A refused verdict is also a refusal of the report, which rule 4 already makes fatal for the whole bundle; the arm fails closed anyway. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "CoverageBasis",
        field: "KernelReplayedClaim",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "The only basis `judge_certificate` accepts, and only when its `certificate` equals the judged certificate's reference (`CertificateCoverageBasisNotThisCertificate` otherwise) and its `family` is classified. The enum is `#[non_exhaustive]`: an unknown basis is `CertificateCoverageUndetermined`. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "KernelClaimFamily",
        field: "ContractGroundDecision",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "The one family `kernel_claim_family` classifies (as `TrustVcNativeKernelClaimFamily::ContractGroundDecision`). The enum is `#[non_exhaustive]`: an unclassified family is `CertificateCoverageUndetermined`, never established. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    // --- DropResolution ----------------------------------------------------
    ProducerField {
        ty: "DropResolution",
        field: "Resolved",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "`direct_callee` (`native_discharge/body.rs`) reads the glue a `Drop` or `DropInvoke` calls, from trust-ir's own `Module::drop_glue_for`, so that a precondition anchored at the drop is attributed to the glue and the recursion walk follows it. It can only make a row the glue's (adjudicated) or add a call edge (a decline); it never licenses a fact.",
    },
    ProducerField {
        ty: "DropResolution",
        field: "Unresolved",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "A drop that names no glue still calls a function: `direct_callee` reports it as unresolved, so a row anchored at it is adjudicated (never excluded) and the recursion walk declines the call.",
    },
    ProducerField {
        ty: "DropResolution",
        field: "Ambiguous",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_discharge/body.rs"],
        note: "Only an unvalidated module answers it; read exactly as `Unresolved`.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "ReportUnchecked",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "CertificateNotInModule",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "ObligationNotInModule",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "NoBasis",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects. `native_coverage/tests.rs` builds it to test that arm.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "KernelUnavailable",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects. `native_coverage/tests.rs` builds it to test that arm.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "ClaimFamilyUnclassified",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage/tests.rs"],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects. `native_coverage/tests.rs` builds it to test that arm.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "NotTheReplayedCertificate",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &["native_coverage.rs", "native_coverage/tests.rs"],
        note: "A sibling certificate on the same obligation was replayed, not this one: `judge_certificate` names it to reject with `CertificateCoverageBasisNotThisCertificate`. `native_coverage/tests.rs` builds verdicts with it to test the rule.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "NoReplayer",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "ReplayInconclusive",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "ObligationNotModeled",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "RequestNotMachineSemantics",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "GoalAnnotationUnbound",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "CoverageUndeterminedReason",
        field: "PremiseNotEstablished",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "Not named by the judge: it reaches `CertificateCoverageUndetermined` through the generic `Undetermined` arm, so it rejects.",
    },
    ProducerField {
        ty: "SpecObligationRef",
        field: "machine",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "Copied into the refusal that `importable_obligation_kind` returns for an obligation attributed to a temporal property, and into the advisory lane's `TemporalPropertyAttributed` refusal. Never a fact.",
    },
    ProducerField {
        ty: "SpecObligationRef",
        field: "temporal",
        kind: ProducerFieldKind::StructField,
        read_sites: &["native_trust_ir_bundle.rs", "trust_ir_body/mod.rs"],
        note: "Copied into the same two refusals as `machine`. Never a fact.",
    },
    ProducerField {
        ty: "TrustMcVerificationMode",
        field: "BoundedModelCheck",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustMcVerificationMode",
        field: "Chc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustMcVerificationMode",
        field: "Pdr",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustWpVerificationMode",
        field: "WeakestPrecondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustWpVerificationMode",
        field: "StrongestPostcondition",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustWpVerificationMode",
        field: "Abduction",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's mode.",
    },
    ProducerField {
        ty: "TrustWpFramePolicy",
        field: "FullHeap",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's frame.",
    },
    ProducerField {
        ty: "TrustWpFramePolicy",
        field: "Minimal",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's frame.",
    },
    ProducerField {
        ty: "TrustWpFramePolicy",
        field: "BorrowRegions",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's frame.",
    },
    ProducerField {
        ty: "TrustWpLoopStrategy",
        field: "RequireInvariants",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's loop strategy.",
    },
    ProducerField {
        ty: "TrustWpLoopStrategy",
        field: "InferInvariants",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's loop strategy.",
    },
    ProducerField {
        ty: "TrustWpLoopStrategy",
        field: "Havoc",
        kind: ProducerFieldKind::NamedPath,
        read_sites: &[],
        note: "NOT READ. Coverage is basis K, the kernel replay of the certificate itself; no bound is derived from a request's loop strategy.",
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    #[expect(
        clippy::unneeded_wildcard_pattern,
        reason = "Named fields preserve the schema inventory; only the inaccessible private field requires the existing rest pattern."
    )]
    /// THE UPSTREAM HALF OF THE RATCHET — a COMPILE-TIME check.
    ///
    /// Each producer type is destructured EXHAUSTIVELY. Add a field upstream and
    /// this stops compiling ("pattern does not mention field"); remove one and
    /// it stops compiling too. Either way the table cannot silently fall behind
    /// the wire format, which is how the round-7 prose list went stale.
    ///
    /// None of these types is `#[non_exhaustive]` at the pinned rev; if one
    /// becomes so, this function stops compiling as well, and the right answer
    /// is to say so here rather than to delete the row.
    #[allow(clippy::used_underscore_binding, clippy::too_many_arguments)]
    fn producer_types_are_exhaustively_enumerated(
        module: &trust_ir::Module,
        function: &trust_ir::Function,
        block: &trust_ir::Block,
        node: &trust_ir::InstrNode,
        obligation: &trust_ir::ProofObligation,
        site: &trust_ir::ObligationSite,
        formula: &trust_ir::ProofFormula,
        identity: &trust_ir::ProofObligationSourceIdentity,
        public: &trust_ir::PublicObligationIdentity,
        certificate: &trust_ir::ProofCertificate,
        context: &trust_ir::proof::ProofContext,
        facts: &trust_ir::NativeCompilerFacts,
        source: &trust_ir::NativeObligationSource,
        request: &trust_ir::request::TrustVcNativeRequest,
        bundle: &trust_ir::request::NativeVerificationBundle,
        target: &trust_ir::TargetInfo,
    ) -> Vec<&'static str> {
        let trust_ir::Module {
            name: _,
            functions: _,
            structs: _,
            enums: _,
            records: _,
            closure_types: _,
            globals: _,
            func_types: _,
            types: _,
            proof_obligations: _,
            proof_certificates: _,
            target_info: _,
            files: _,
            obligation_diagnostics: _,
            spec_modules: _,
            universes: _,
            predicates: _,
            global_asm: _,
            imports: _,
            tuple_layouts: _,
            completeness: _,
            drop_glue: _,
            closure_layouts: _,
            blobs: _,
        } = module;
        let trust_ir::Function {
            id: _,
            name: _,
            ty: _,
            entry: _,
            blocks: _,
            proofs: _,
            calling_conv: _,
            linkage: _,
            attrs: _,
            summary: _,
            producer: _,
            value_names: _,
            scopes: _,
            source_provenance: _,
            body_gate: _,
            display_path: _,
            section: _,
            visibility: _,
            retained: _,
        } = function;
        let trust_ir::Block {
            id: _,
            params: _,
            body: _,
        } = block;
        let trust_ir::InstrNode {
            inst: _,
            results: _,
            proofs: _,
            span: _,
            proof_context: _,
            scope: _,
        } = node;
        let trust_ir::ProofObligation {
            id: _,
            kind: _,
            status: _,
            description: _,
            formula: _,
            function: _,
            source: _,
            site: _,
            spec: _,
        } = obligation;
        let trust_ir::ObligationSite {
            function: _,
            block: _,
            inst_index: _,
        } = site;
        let trust_ir::ProofFormula {
            schema: _,
            payload: _,
            smtlib: _,
            sort: _,
            bindings: _,
        } = formula;
        let trust_ir::ProofObligationSourceIdentity {
            source_id: _,
            assertion_id: _,
            range: _,
            public: _,
        } = identity;
        let trust_ir::PublicObligationIdentity {
            obligation_id: _,
            semantic_digest: _,
        } = public;
        let trust_ir::ProofCertificate {
            obligation: _,
            prover: _,
            evidence: _,
            assurance: _,
        } = certificate;
        let trust_ir::proof::ProofContext {
            assumes: _,
            establishes: _,
        } = context;
        let trust_ir::NativeCompilerFacts {
            adt_layouts: _,
            fat_pointers: _,
            trait_object_metadata: _,
            pointer_offsets: _,
            casts: _,
            monomorphizations: _,
            obligation_sources: _,
        } = facts;
        let trust_ir::NativeObligationSource {
            obligation: _,
            public_obligation_id: _,
            function: _,
            span: _,
            assertion_id: _,
            cause: _,
            monomorphization: _,
            facts: _,
        } = source;
        let trust_ir::request::TrustVcNativeRequest {
            id: _,
            mode: _,
            obligations: _,
            certificates: _,
            lineage_roots: _,
            options: _,
            diagnostics: _,
            provenance: _,
            function: _,
        } = request;
        let trust_ir::request::NativeVerificationBundle {
            schema_version: _,
            producer: _,
            input: _,
            provenance: _,
            serialization: _,
            diagnostics: _,
            trust_ir_module_digest: _,
            compiler_facts: _,
            module: _,
            lineage: _,
            requests: _,
            evidence_bundles: _,
            // `NativeVerificationBundle` carries one PRIVATE field,
            // `source_generation_live` — a transient identity upstream keeps
            // inaccessible on purpose, and which safe downstream code therefore
            // cannot read. `..` is forced here and ONLY here; the cost is that a
            // new PUBLIC field on this one type would not break the build, so
            // the read-site scan is the ratchet for that one type.
            ..
        } = bundle;
        let trust_ir::TargetInfo {
            triple: _,
            pointer_size: _,
            endianness: _,
            abi: _,
            struct_passing: _,
        } = target;
        vec![
            "Module",
            "Function",
            "Block",
            "InstrNode",
            "ProofObligation",
            "ObligationSite",
            "ProofFormula",
            "ProofObligationSourceIdentity",
            "PublicObligationIdentity",
            "ProofCertificate",
            "ProofContext",
            "NativeCompilerFacts",
            "NativeObligationSource",
            "TrustVcNativeRequest",
            "NativeVerificationBundle",
            "TargetInfo",
        ]
    }

    #[expect(
        clippy::single_match,
        reason = "Explicit current variants and documented non-exhaustive fallbacks are the schema check."
    )]
    /// THE UPSTREAM HALF OF THE RATCHET, SECOND FUNCTION — the VALUE types.
    ///
    /// ROUND 9's major: the first function pins sixteen types a person typed,
    /// and the read-site scan iterates over the fields ALREADY IN THE TABLE, so
    /// a field of an UN-TABLED type could gain read sites and neither ratchet
    /// would notice. A mechanical scan found 59 `trust_ir` types named by this
    /// crate's own sources and 43 outside the pinned sixteen — including `Inst`
    /// (the entire program semantics), `ProofEvidence` (whose `CleanCic { term,
    /// lineage, .. }` IS the round-5/7 kernel-recheck guard),
    /// `NativeRequestProvenance` (which decides MissingSuiteIdentity /
    /// MissingSolverIdentity / MissingReplayTranscriptDigest on every artifact)
    /// and `NativeVerificationBundleError` (one variant of which this lane
    /// destructures to carry an upstream refusal PAST).
    ///
    /// Every one of them is enumerated here, exhaustively, and the type closure
    /// itself is now checked by
    /// `every_trust_ir_type_this_crate_names_is_tabled_or_excluded`.
    ///
    /// Enums are matched with every variant and every field of every variant
    /// named: a variant added upstream, or a field added to a variant, stops
    /// this compiling. Opaque ids are destructured as the one-field newtypes
    /// they are, which is the WITNESS for their entry in
    /// [`UNTABLED_PRODUCER_TYPES`].
    #[allow(
        clippy::used_underscore_binding,
        clippy::too_many_lines,
        clippy::too_many_arguments
    )]
    fn producer_value_types_are_exhaustively_enumerated(
        inst_value: &trust_ir::Inst,
        ty_value: &trust_ir::Ty,
        constant_value: &trust_ir::Constant,
        proofevidence_value: &trust_ir::ProofEvidence,
        nativeverificationbundleerror_value: &trust_ir::request::NativeVerificationBundleError,
        nativecompilerfactref_value: &trust_ir::request::NativeCompilerFactRef,
        nativeadapterinput_value: &trust_ir::request::NativeAdapterInput,
        nativeverificationrequest_value: &trust_ir::request::NativeVerificationRequest,
        obligationkind_value: &trust_ir::ObligationKind,
        proofstatus_value: &trust_ir::ProofStatus,
        clausesort_value: &trust_ir::proof::ClauseSort,
        nativeobligationcause_value: &trust_ir::request::NativeObligationCause,
        trustvcverificationmode_value: &trust_ir::request::TrustVcVerificationMode,
        nativeverifiersuite_value: &trust_ir::request::NativeVerifierSuite,
        nativeevidenceartifactkind_value: &trust_ir::request::NativeEvidenceArtifactKind,
        nativebundleproducer_value: &trust_ir::request::NativeBundleProducer,
        callingconv_value: &trust_ir::CallingConv,
        endianness_value: &trust_ir::Endianness,
        structpassingpolicy_value: &trust_ir::StructPassingPolicy,
        binop_value: &trust_ir::BinOp,
        unop_value: &trust_ir::UnOp,
        icmpop_value: &trust_ir::ICmpOp,
        overflowop_value: &trust_ir::OverflowOp,
        castop_value: &trust_ir::CastOp,
        functy_value: &trust_ir::FuncTy,
        closurety_value: &trust_ir::ClosureTy,
        storage_value: &trust_ir::StorageLayout,
        switchcase_value: &trust_ir::SwitchCase,
        sourcespan_value: &trust_ir::SourceSpan,
        prooflineagenode_value: &trust_ir::ProofLineageNode,
        proofcertificateref_value: &trust_ir::ProofCertificateRef,
        proofreplayidentity_value: &trust_ir::proof::ProofReplayIdentity,
        nativerequestprovenance_value: &trust_ir::request::NativeRequestProvenance,
        nativeevidenceartifact_value: &trust_ir::request::NativeEvidenceArtifact,
        nativetoolidentity_value: &trust_ir::request::NativeToolIdentity,
        trustvcnativeevidencebundle_value: &trust_ir::request::TrustVcNativeEvidenceBundle,
        proofdigest_value: &trust_ir::ProofDigest,
        valueid_value: &trust_ir::ValueId,
        blockid_value: &trust_ir::BlockId,
        funcid_value: &trust_ir::FuncId,
        functyid_value: &trust_ir::FuncTyId,
        tyid_value: &trust_ir::TyId,
        proofid_value: &trust_ir::ProofId,
        prooflineageid_value: &trust_ir::ProofLineageId,
        nativeassertionid_value: &trust_ir::request::NativeAssertionId,
        nativereplaycontext_value: &trust_ir::request::NativeReplayContext,
        nativereplayatom_value: &trust_ir::request::NativeReplayAtom,
        nativereplayatomkind_value: &trust_ir::request::NativeReplayAtomKind,
        nativereplayatomid_value: &trust_ir::request::NativeReplayAtomId,
        interpretoptions_value: &trust_ir::InterpretOptions,
        interpretvalue_value: &trust_ir::InterpretValue,
        interpreterrorcode_value: &trust_ir::InterpretErrorCode,
        funcattrs_value: &trust_ir::FuncAttrs,
        linkage_value: &trust_ir::Linkage,
        proofdigestalgorithm_value: &trust_ir::ProofDigestAlgorithm,
        coverageassurance_value: &trust_ir::proof::CoverageAssurance,
        coveragebound_value: &trust_ir::proof::CoverageBound,
        specobligationref_value: &trust_ir::proof::SpecObligationRef,
        trustmcverificationmode_value: &trust_ir::request::TrustMcVerificationMode,
        trustwpverificationmode_value: &trust_ir::request::TrustWpVerificationMode,
        trustwpframepolicy_value: &trust_ir::request::TrustWpFramePolicy,
        trustwploopstrategy_value: &trust_ir::request::TrustWpLoopStrategy,
        visibility_value: &trust_ir::Visibility,
        coverageinputs_value: &trust_ir_build::CoverageInputs<'_>,
        certificatecoverage_value: &trust_ir_build::CertificateCoverage,
        coveragebasis_value: &trust_ir_build::CoverageBasis,
        coverageundeterminedreason_value: &trust_ir_build::CoverageUndeterminedReason,
        kernelclaimfamily_value: &trust_ir::proof::KernelClaimFamily,
        dropresolution_value: &trust_ir::DropResolution,
        boxpointee_value: &trust_ir::box_validity::BoxPointee,
        boxvalidityfact_value: &trust_ir::box_validity::BoxValidityFact,
        boxderefsite_value: &trust_ir::box_validity::BoxDerefSite,
        boxfactsession_value: &trust_ir::box_validity::BoxFactSession,
        premiseroot_value: &trust_ir::box_validity::PremiseRoot,
    ) -> Vec<&'static str> {
        match inst_value {
            trust_ir::Inst::BinOp {
                op: _,
                ty: _,
                lhs: _,
                rhs: _,
            } => {}
            trust_ir::Inst::UnOp {
                op: _,
                ty: _,
                operand: _,
            } => {}
            trust_ir::Inst::Overflow {
                op: _,
                ty: _,
                lhs: _,
                rhs: _,
            } => {}
            trust_ir::Inst::ICmp {
                op: _,
                ty: _,
                lhs: _,
                rhs: _,
            } => {}
            trust_ir::Inst::FCmp {
                op: _,
                ty: _,
                lhs: _,
                rhs: _,
            } => {}
            trust_ir::Inst::Cast {
                op: _,
                src_ty: _,
                dst_ty: _,
                operand: _,
            } => {}
            trust_ir::Inst::BoxDeref {
                ptr_ty: _,
                pointee: _,
                operand: _,
                fact: _,
            } => {}
            trust_ir::Inst::Load {
                ty: _,
                ptr: _,
                volatile: _,
                align: _,
            } => {}
            trust_ir::Inst::Store {
                ty: _,
                ptr: _,
                value: _,
                volatile: _,
                align: _,
            } => {}
            trust_ir::Inst::Alloca {
                ty: _,
                count: _,
                align: _,
            } => {}
            trust_ir::Inst::HeapAlloc {
                ty: _,
                count: _,
                align: _,
                origin: _,
            } => {}
            trust_ir::Inst::GEP {
                pointee_ty: _,
                base: _,
                indices: _,
                inbounds: _,
            } => {}
            trust_ir::Inst::PtrData { ptr_ty: _, ptr: _ } => {}
            trust_ir::Inst::PtrMetadata {
                ptr_ty: _,
                metadata_ty: _,
                ptr: _,
            } => {}
            trust_ir::Inst::PtrFromParts {
                ptr_ty: _,
                metadata_ty: _,
                data: _,
                metadata: _,
            } => {}
            trust_ir::Inst::AtomicLoad {
                ty: _,
                ptr: _,
                ordering: _,
            } => {}
            trust_ir::Inst::AtomicStore {
                ty: _,
                ptr: _,
                value: _,
                ordering: _,
            } => {}
            trust_ir::Inst::AtomicRMW {
                op: _,
                ty: _,
                ptr: _,
                value: _,
                ordering: _,
            } => {}
            trust_ir::Inst::CmpXchg {
                ty: _,
                ptr: _,
                expected: _,
                desired: _,
                success: _,
                failure: _,
                weak: _,
            } => {}
            trust_ir::Inst::Fence { ordering: _ } => {}
            trust_ir::Inst::Br { target: _, args: _ } => {}
            trust_ir::Inst::CondBr {
                cond: _,
                then_target: _,
                then_args: _,
                else_target: _,
                else_args: _,
            } => {}
            trust_ir::Inst::Switch {
                value: _,
                default: _,
                default_args: _,
                cases: _,
                exhaustive_enum_unreachable: _,
            } => {}
            trust_ir::Inst::Call { callee: _, args: _ } => {}
            trust_ir::Inst::CallIndirect {
                callee: _,
                sig: _,
                args: _,
                calling_conv: _,
            } => {}
            trust_ir::Inst::Return { values: _ } => {}
            trust_ir::Inst::ExtractField {
                ty: _,
                aggregate: _,
                field: _,
            } => {}
            trust_ir::Inst::InsertField {
                ty: _,
                aggregate: _,
                field: _,
                value: _,
            } => {}
            trust_ir::Inst::ExtractElement {
                ty: _,
                array: _,
                index: _,
            } => {}
            trust_ir::Inst::InsertElement {
                ty: _,
                array: _,
                index: _,
                value: _,
            } => {}
            trust_ir::Inst::Const { ty: _, value: _ } => {}
            trust_ir::Inst::NullPtr => {}
            trust_ir::Inst::GlobalAddr { global: _ } => {}
            trust_ir::Inst::Undef { ty: _ } => {}
            trust_ir::Inst::Assume { cond: _ } => {}
            trust_ir::Inst::Assert {
                cond: _,
                kind: _,
                site: _,
            } => {}
            trust_ir::Inst::Unreachable => {}
            trust_ir::Inst::MemCopy {
                dst: _,
                src: _,
                bytes: _,
                overlap: _,
            } => {}
            trust_ir::Inst::MemSet {
                dst: _,
                byte: _,
                bytes: _,
            } => {}
            trust_ir::Inst::MakeAggregate {
                ty: _,
                variant: _,
                fields: _,
            } => {}
            trust_ir::Inst::MakeClosure {
                ty: _,
                func: _,
                captures: _,
            } => {}
            trust_ir::Inst::Copy { ty: _, operand: _ } => {}
            trust_ir::Inst::Select {
                ty: _,
                cond: _,
                then_val: _,
                else_val: _,
            } => {}
            trust_ir::Inst::SeqMapAddK {
                ty: _,
                seq: _,
                k: _,
            } => {}
            trust_ir::Inst::SeqMapNot { ty: _, seq: _ } => {}
            trust_ir::Inst::SeqMap {
                ty: _,
                seq: _,
                fwd: _,
            } => {}
            trust_ir::Inst::Borrow { ptr: _ } => {}
            trust_ir::Inst::BorrowMut { ptr: _ } => {}
            trust_ir::Inst::EndBorrow { borrow_ptr: _ } => {}
            trust_ir::Inst::Retain { ptr: _ } => {}
            trust_ir::Inst::Release { ptr: _ } => {}
            trust_ir::Inst::IsUnique { ptr: _ } => {}
            trust_ir::Inst::Dealloc { ptr: _ } => {}
            trust_ir::Inst::OpenFrame { def: _ } => {}
            trust_ir::Inst::BindSlot {
                frame: _,
                slot: _,
                value: _,
            } => {}
            trust_ir::Inst::LoadSlot {
                frame: _,
                slot: _,
                ty: _,
            } => {}
            trust_ir::Inst::CloseFrame { frame: _ } => {}
            trust_ir::Inst::CoroSuspend {
                frame: _,
                state_slot: _,
                next_state: _,
                value: _,
            } => {}
            trust_ir::Inst::Invoke {
                callee: _,
                args: _,
                normal_dest: _,
                normal_args: _,
                unwind_dest: _,
            } => {}
            trust_ir::Inst::LandingPad {
                is_cleanup: _,
                catch_type_indices: _,
            } => {}
            trust_ir::Inst::Resume { exn: _ } => {}
            trust_ir::Inst::Drop { ty: _, ptr: _ } => {}
            trust_ir::Inst::ArraySplat { ty: _, value: _ } => {}
            trust_ir::Inst::DialectOp(_) => {}
            trust_ir::Inst::AssertInvoke {
                cond: _,
                kind: _,
                site: _,
                normal_dest: _,
                normal_args: _,
                unwind_dest: _,
            } => {}
            trust_ir::Inst::CallCannotUnwind { callee: _, args: _ } => {}
            trust_ir::Inst::CallIndirectCannotUnwind {
                callee: _,
                sig: _,
                args: _,
                calling_conv: _,
            } => {}
            trust_ir::Inst::DropInvoke {
                ty: _,
                ptr: _,
                normal_dest: _,
                normal_args: _,
                unwind_dest: _,
            } => {}
            trust_ir::Inst::InvokeIndirect {
                callee: _,
                sig: _,
                args: _,
                calling_conv: _,
                normal_dest: _,
                normal_args: _,
                unwind_dest: _,
            } => {}
            trust_ir::Inst::TensorContract {
                ty: _,
                lhs: _,
                rhs: _,
                batch: _,
                contract: _,
            } => {}
            trust_ir::Inst::TensorMap {
                ty: _,
                args: _,
                body: _,
            } => {}
            trust_ir::Inst::TensorReduce {
                ty: _,
                src: _,
                op: _,
                axes: _,
                order: _,
            } => {}
            trust_ir::Inst::TensorView {
                ty: _,
                src: _,
                params: _,
                exprs: _,
                shape: _,
                index: _,
                fill: _,
            } => {}
            trust_ir::Inst::TensorGather {
                ty: _,
                data: _,
                coords: _,
            } => {}
            trust_ir::Inst::TensorScatter {
                ty: _,
                init: _,
                src: _,
                coords: _,
            } => {}
        }
        match ty_value {
            trust_ir::Ty::I8 => {}
            trust_ir::Ty::I16 => {}
            trust_ir::Ty::I32 => {}
            trust_ir::Ty::I64 => {}
            trust_ir::Ty::I128 => {}
            trust_ir::Ty::U8 => {}
            trust_ir::Ty::U16 => {}
            trust_ir::Ty::U32 => {}
            trust_ir::Ty::U64 => {}
            trust_ir::Ty::U128 => {}
            trust_ir::Ty::Isize => {}
            trust_ir::Ty::Usize => {}
            trust_ir::Ty::Char => {}
            trust_ir::Ty::Error => {}
            trust_ir::Ty::F16 => {}
            trust_ir::Ty::F32 => {}
            trust_ir::Ty::F64 => {}
            trust_ir::Ty::Bool => {}
            trust_ir::Ty::Vector(_, _) => {}
            trust_ir::Ty::Ptr => {}
            trust_ir::Ty::FatPtr(_) => {}
            trust_ir::Ty::Unit => {}
            trust_ir::Ty::Never => {}
            trust_ir::Ty::Struct(_) => {}
            trust_ir::Ty::Array(_, _) => {}
            trust_ir::Ty::Tuple(_) => {}
            trust_ir::Ty::Enum(_) => {}
            trust_ir::Ty::Func(_) => {}
            trust_ir::Ty::Ref(_) => {}
            trust_ir::Ty::RefMut(_) => {}
            trust_ir::Ty::PtrConst(_) => {}
            trust_ir::Ty::PtrMut(_) => {}
            trust_ir::Ty::Rc(_) => {}
            trust_ir::Ty::Set(_, _) => {}
            trust_ir::Ty::Sequence(_) => {}
            trust_ir::Ty::Record(_) => {}
            trust_ir::Ty::Closure(_) => {}
            trust_ir::Ty::Refine(_, _) => {}
            trust_ir::Ty::Dialect(_) => {}
            trust_ir::Ty::Handle(_) => {}
            trust_ir::Ty::FnItem(_) => {}
            trust_ir::Ty::Storage(_) => {}
            trust_ir::Ty::Tensor(_, _) => {}
            trust_ir::Ty::Ext(never) => never.unreachable(),
        }
        match constant_value {
            trust_ir::Constant::Int(_) => {}
            trust_ir::Constant::U128(_) => {}
            trust_ir::Constant::Bytes { data: _, utf8: _ } => {}
            trust_ir::Constant::Float(_) => {}
            trust_ir::Constant::Bool(_) => {}
            trust_ir::Constant::Aggregate(_) => {}
            trust_ir::Constant::Array(_) => {}
            trust_ir::Constant::Vector(_) => {}
            trust_ir::Constant::Sequence(_) => {}
            trust_ir::Constant::Set(_) => {}
            trust_ir::Constant::Record(_) => {}
            trust_ir::Constant::Closure {
                func: _,
                captures: _,
            } => {}
            trust_ir::Constant::FnDef(_) => {}
            trust_ir::Constant::SymbolAddr {
                symbol: _,
                addend: _,
            } => {}
            trust_ir::Constant::PhantomData => {}
            trust_ir::Constant::Uninit => {}
            trust_ir::Constant::Splat { elem: _, len: _ } => {}
            trust_ir::Constant::Ext(never) => never.unreachable(),
            trust_ir::Constant::FnItem(_) => {}
            trust_ir::Constant::TensorBlob { digest: _, dims: _ } => {}
        }
        match proofevidence_value {
            trust_ir::ProofEvidence::SmtProof(_) => {}
            trust_ir::ProofEvidence::LeanProof(_) => {}
            trust_ir::ProofEvidence::KaniHarness(_) => {}
            trust_ir::ProofEvidence::GammaCrownBound {
                epsilon: _,
                verified_layers: _,
            } => {}
            trust_ir::ProofEvidence::TranslationValidation {
                rule_name: _,
                smt_hash: _,
            } => {}
            trust_ir::ProofEvidence::Trusted(_) => {}
            trust_ir::ProofEvidence::InheritedFromCallee {
                callee: _,
                obligation: _,
                external: _,
            } => {}
            trust_ir::ProofEvidence::CleanCic {
                term: _,
                context: _,
                lineage: _,
                kernel_recheck: _,
            } => {}
        }
        match nativeverificationbundleerror_value {
            trust_ir::request::NativeVerificationBundleError::UnsupportedSchemaVersion(_) => {}
            trust_ir::request::NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(_) => {}
            trust_ir::request::NativeVerificationBundleError::EmptyRequests => {}
            trust_ir::request::NativeVerificationBundleError::EmptyDigest { field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::NonCryptographicDigest { field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustIrModuleDigestMismatch { expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustIrModuleHasNoWireIdentity { location: _, construct: _ } => {}
            trust_ir::request::NativeVerificationBundleError::RustReferenceAsPermissionBorrow { location: _ } => {}
            trust_ir::request::NativeVerificationBundleError::BundlePrimaryLanguageUncovered { primary: _, source_languages: _ } => {}
            trust_ir::request::NativeVerificationBundleError::BundleLanguageUncovered { producer: _, functions: _, source_languages: _ } => {}
            trust_ir::request::NativeVerificationBundleError::BundleImportLanguageUncovered { import: _, name: _, producer: _, source_languages: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EmptyProvenanceField(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidToolIdentityField { field: _, component: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InputDigestMismatch { field: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::NonCanonicalSerialization(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy { field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidDiagnosticsPolicy { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::VerifierSuiteMismatch { request: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ExpectedVerifierIdentityMismatch { request: _, suite: _, verifier: _, canonical: _ } => {}
            trust_ir::request::NativeVerificationBundleError::SourceDigestNotInLineage(_) => {}
            trust_ir::request::NativeVerificationBundleError::TrustIrDigestNotInLineage(_) => {}
            trust_ir::request::NativeVerificationBundleError::Lineage(_) => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateRequestId(_) => {}
            trust_ir::request::NativeVerificationBundleError::EmptyRequestObligations(_) => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateRequestObligation { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownRequestObligation { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EmptyLineageRoots(_) => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateRequestLineageRoot { request: _, root: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownLineageRoot { request: _, root: _ } => {}
            trust_ir::request::NativeVerificationBundleError::RequestLineageRootTargetMismatch { request: _, root: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::RequestSourceDigestNotInLineage { request: _, source: _ } => {}
            trust_ir::request::NativeVerificationBundleError::RequestObligationNotInLineage { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingFunction { request: _, function: _ } => {}
            trust_ir::request::NativeVerificationBundleError::RequestObligationFunctionMismatch { request: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingCertificate { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::CertificateDigestMismatch { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::CertificateObligationNotRequested { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateRequestCertificate { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::CertificateNotInLineage { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::CertificateVerifierSuiteMismatch { request: _, expected: _, obligation: _, prover: _, canonical: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingTrustVcEvidenceForObligation { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustedCertificateRejected { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustVcCertificateNotDischarged { request: _, obligation: _, prover: _, status: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingReplayIdentity(_) => {}
            trust_ir::request::NativeVerificationBundleError::MissingReplayTranscriptDigest(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidReplayIdentity { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ReplayIdentityVerifierSuiteMismatch { request: _, expected: _, engine: _, canonical: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateReplayAtomId { request: _, atom: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidReplayAtom { request: _, atom: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ReplayAtomDigestMismatch { request: _, atom: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ReplayAtomObligationNotRequested { request: _, atom: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ReplayAtomAssertionMismatch { request: _, atom: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ReplayAtomSourceSpanMismatch { request: _, atom: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnsupportedNativeRequestMode { request: _, reason: _, detail: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingTrustWpStrongestPostconditionContext(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidTrustMcBmcOptions { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidTrustMcChcOptions { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidTrustWpOptions { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateModuleObligationId(_) => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateCompilerFactId(_) => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateMonomorphizationId(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidCompilerFact { fact: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownCompilerFactFunction { fact: _, function: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownCompilerFactObligation { fact: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateObligationSource(_) => {}
            trust_ir::request::NativeVerificationBundleError::InvalidPublicObligationId { obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicatePublicObligationSource { public_obligation_id: _, first_obligation: _, duplicate_obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownObligationSource(_) => {}
            trust_ir::request::NativeVerificationBundleError::UnknownObligationSourceFunction { obligation: _, function: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSource { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingEmbeddedObligationSource { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingEmbeddedPublicObligationIdentity { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidEmbeddedObligationSource { request: _, obligation: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EmbeddedPublicObligationIdMismatch { request: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EmbeddedObligationSourceSpanMismatch { request: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSourceSpan { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSourceAssertion { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownMonomorphization { obligation: _, monomorphization: _ } => {}
            trust_ir::request::NativeVerificationBundleError::UnknownCompilerFactReference { obligation: _, fact: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSourceCastFact { obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSourcePointerOffsetFact { obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingObligationSourceTraitObjectMetadataFact { obligation: _, fat_pointer: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ObligationSourceFactMonomorphizationMismatch { obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ObligationSourceFactFunctionMismatch { obligation: _, fact: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::ObligationSourceFactObligationMismatch { obligation: _, fact: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateEvidenceBundle { request: _, suite: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceRequestUnknown { request: _, suite: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceRequestMismatch { request: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceTrustIrModuleDigestMismatch { request: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceRequestDigestMismatch { request: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceProvenanceMismatch { request: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceObligationMismatch { request: _, obligation: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingEvidenceArtifacts { request: _, suite: _ } => {}
            trust_ir::request::NativeVerificationBundleError::DuplicateEvidenceArtifact { request: _, name: _ } => {}
            trust_ir::request::NativeVerificationBundleError::InvalidEvidenceArtifact { request: _, name: _, field: _ } => {}
            trust_ir::request::NativeVerificationBundleError::EvidenceArtifactSuiteMismatch { request: _, suite: _, kind: _ } => {}
            trust_ir::request::NativeVerificationBundleError::MissingTrustVcDischargeFunction(_) => {}
            trust_ir::request::NativeVerificationBundleError::TrustVcDischargeRequestCarriesCertificate { request: _, obligation: _, prover: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustVcDischargeObligationNotSitedInFunction { request: _, obligation: _, expected: _, actual: _ } => {}
            trust_ir::request::NativeVerificationBundleError::TrustVcObligationBothImportedAndDischarged { obligation: _, importing: _, discharging: _ } => {}
            trust_ir::request::NativeVerificationBundleError::FormulaTextsDisagree { site: _ } => {}
        }
        match nativecompilerfactref_value {
            trust_ir::request::NativeCompilerFactRef::AdtLayout(_) => {}
            trust_ir::request::NativeCompilerFactRef::FatPointer(_) => {}
            trust_ir::request::NativeCompilerFactRef::TraitObjectMetadata(_) => {}
            trust_ir::request::NativeCompilerFactRef::PointerOffset(_) => {}
            trust_ir::request::NativeCompilerFactRef::Cast(_) => {}
            trust_ir::request::NativeCompilerFactRef::Monomorphization(_) => {}
        }
        match nativeadapterinput_value {
            trust_ir::request::NativeAdapterInput::RustMir { body_digest: _ } => {}
            trust_ir::request::NativeAdapterInput::RustThir { source_digest: _ } => {}
            trust_ir::request::NativeAdapterInput::TrustIrModule => {}
        }
        match nativeverificationrequest_value {
            trust_ir::request::NativeVerificationRequest::TrustVc(_) => {}
            trust_ir::request::NativeVerificationRequest::TrustMc(_) => {}
            trust_ir::request::NativeVerificationRequest::TrustWp(_) => {}
        }
        match obligationkind_value {
            trust_ir::ObligationKind::Precondition => {}
            trust_ir::ObligationKind::Postcondition => {}
            trust_ir::ObligationKind::LoopInvariant => {}
            trust_ir::ObligationKind::TypeInvariant => {}
            trust_ir::ObligationKind::RefinementType => {}
            trust_ir::ObligationKind::TranslationValidation => {}
            trust_ir::ObligationKind::MemorySafety => {}
            trust_ir::ObligationKind::PanicFreedom => {}
            trust_ir::ObligationKind::TemporalSafety => {}
            trust_ir::ObligationKind::Liveness => {}
            trust_ir::ObligationKind::ArithmeticSafety => {}
            trust_ir::ObligationKind::BoundsCheck => {}
            trust_ir::ObligationKind::GiveBackRefinement => {}
            trust_ir::ObligationKind::Termination => {}
            trust_ir::ObligationKind::Ownership => {}
            trust_ir::ObligationKind::Custom {
                namespace: _,
                name: _,
            } => {}
            // `ObligationKind` is `#[non_exhaustive]` at this pin, as is
            // `CoverageBound` below (upstream's own comment: the spine
            // grows routing-grade panic-class kinds without a lockstep break).
            // The wildcard is forced, so the COMPILE-TIME half cannot pin this
            // type's variant list: a new kind reaches this crate silently.
            // What still holds: the table's rows are checked against the crate
            // by the read-site scan, and the lane's own dispatch treats a kind
            // it does not name as UNMODELLED — it never falls through to a
            // modelled arm.
            _ => {}
        }
        match proofstatus_value {
            trust_ir::ProofStatus::Pending => {}
            trust_ir::ProofStatus::Discharged => {}
            trust_ir::ProofStatus::Failed => {}
            trust_ir::ProofStatus::Trusted => {}
            trust_ir::ProofStatus::Certified => {}
        }
        match clausesort_value {
            trust_ir::proof::ClauseSort::Bool => {}
            trust_ir::proof::ClauseSort::Int => {}
            trust_ir::proof::ClauseSort::BitVec(_) => {}
            trust_ir::proof::ClauseSort::Array(_, _) => {}
            trust_ir::proof::ClauseSort::Float { eb: _, sb: _ } => {}
            trust_ir::proof::ClauseSort::RoundingMode => {}
            trust_ir::proof::ClauseSort::Datatype {
                name: _,
                constructors: _,
            } => {}
        }
        match nativeobligationcause_value {
            trust_ir::request::NativeObligationCause::Precondition => {}
            trust_ir::request::NativeObligationCause::Postcondition => {}
            trust_ir::request::NativeObligationCause::Assert => {}
            trust_ir::request::NativeObligationCause::BoundsCheck => {}
            trust_ir::request::NativeObligationCause::OverflowCheck => {}
            trust_ir::request::NativeObligationCause::LayoutCheck => {}
            trust_ir::request::NativeObligationCause::CastCheck => {}
            trust_ir::request::NativeObligationCause::PointerOffset => {}
            trust_ir::request::NativeObligationCause::BorrowCheck => {}
            trust_ir::request::NativeObligationCause::Translation => {}
            trust_ir::request::NativeObligationCause::Panic => {}
            trust_ir::request::NativeObligationCause::Temporal => {}
            trust_ir::request::NativeObligationCause::Other => {}
        }
        match trustvcverificationmode_value {
            trust_ir::request::TrustVcVerificationMode::ImportProofCertificates => {}
            trust_ir::request::TrustVcVerificationMode::MergeProofCertificates => {}
            trust_ir::request::TrustVcVerificationMode::DischargeProofObligations => {}
        }
        match nativeverifiersuite_value {
            trust_ir::request::NativeVerifierSuite::Unknown => {}
            trust_ir::request::NativeVerifierSuite::TrustVc => {}
            trust_ir::request::NativeVerifierSuite::TrustMc => {}
            trust_ir::request::NativeVerifierSuite::TrustWp => {}
            trust_ir::request::NativeVerifierSuite::AY => {}
            trust_ir::request::NativeVerifierSuite::TRust => {}
            trust_ir::request::NativeVerifierSuite::TrustIr => {}
            trust_ir::request::NativeVerifierSuite::Other => {}
        }
        match nativeevidenceartifactkind_value {
            trust_ir::request::NativeEvidenceArtifactKind::TrustVcCertificateImport => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustVcMergedCertificate => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustMcHornClauses => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustMcPdrTrace => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustMcModel => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustWpVerificationCondition => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustWpReplayTrace => {}
            trust_ir::request::NativeEvidenceArtifactKind::TrustWpAbducedPrecondition => {}
            trust_ir::request::NativeEvidenceArtifactKind::ReplayTranscript => {}
            trust_ir::request::NativeEvidenceArtifactKind::Other => {}
            trust_ir::request::NativeEvidenceArtifactKind::Btor2Trace => {}
            trust_ir::request::NativeEvidenceArtifactKind::Btor2Proof => {}
            trust_ir::request::NativeEvidenceArtifactKind::NativeCompiledArtifact => {}
            trust_ir::request::NativeEvidenceArtifactKind::BackendCapabilityMetadata => {}
        }
        match nativebundleproducer_value {
            trust_ir::request::NativeBundleProducer::TRust => {}
            trust_ir::request::NativeBundleProducer::TSwift => {}
            trust_ir::request::NativeBundleProducer::TC => {}
            trust_ir::request::NativeBundleProducer::TrustIr => {}
            trust_ir::request::NativeBundleProducer::Clean => {}
        }
        match callingconv_value {
            trust_ir::CallingConv::C => {}
            trust_ir::CallingConv::Fast => {}
            trust_ir::CallingConv::Cold => {}
            trust_ir::CallingConv::Rust => {}
            trust_ir::CallingConv::Swift => {}
            trust_ir::CallingConv::CUnwind => {}
            trust_ir::CallingConv::SysV64 => {}
            trust_ir::CallingConv::Win64 => {}
            trust_ir::CallingConv::Aapcs => {}
            trust_ir::CallingConv::EfiApi => {}
            trust_ir::CallingConv::VectorCall => {}
            trust_ir::CallingConv::RustCold => {}
        }
        match endianness_value {
            trust_ir::Endianness::Little => {}
            trust_ir::Endianness::Big => {}
        }
        match structpassingpolicy_value {
            trust_ir::StructPassingPolicy::NativeC => {}
            trust_ir::StructPassingPolicy::AlwaysMemory => {}
            trust_ir::StructPassingPolicy::Unclassified => {}
        }
        match binop_value {
            trust_ir::BinOp::Add => {}
            trust_ir::BinOp::Sub => {}
            trust_ir::BinOp::Mul => {}
            trust_ir::BinOp::UDiv => {}
            trust_ir::BinOp::SDiv => {}
            trust_ir::BinOp::URem => {}
            trust_ir::BinOp::SRem => {}
            trust_ir::BinOp::FAdd => {}
            trust_ir::BinOp::FSub => {}
            trust_ir::BinOp::FMul => {}
            trust_ir::BinOp::FDiv => {}
            trust_ir::BinOp::FRem => {}
            trust_ir::BinOp::FMin => {}
            trust_ir::BinOp::FMax => {}
            trust_ir::BinOp::And => {}
            trust_ir::BinOp::Or => {}
            trust_ir::BinOp::Xor => {}
            trust_ir::BinOp::Shl => {}
            trust_ir::BinOp::LShr => {}
            trust_ir::BinOp::AShr => {}
            trust_ir::BinOp::BAnd => {}
            trust_ir::BinOp::BOr => {}
            trust_ir::BinOp::BXor => {}
            trust_ir::BinOp::RotL => {}
            trust_ir::BinOp::RotR => {}
            trust_ir::BinOp::FCopySign => {}
        }
        match unop_value {
            trust_ir::UnOp::Neg => {}
            trust_ir::UnOp::FNeg => {}
            trust_ir::UnOp::FAbs => {}
            trust_ir::UnOp::FSqrt => {}
            trust_ir::UnOp::FFloor => {}
            trust_ir::UnOp::FCeil => {}
            trust_ir::UnOp::FTrunc => {}
            trust_ir::UnOp::Not => {}
            trust_ir::UnOp::CtPop => {}
            trust_ir::UnOp::CtLz => {}
            trust_ir::UnOp::CtTz => {}
            trust_ir::UnOp::BSwap => {}
            trust_ir::UnOp::BitReverse => {}
        }
        match icmpop_value {
            trust_ir::ICmpOp::Eq => {}
            trust_ir::ICmpOp::Ne => {}
            trust_ir::ICmpOp::Ult => {}
            trust_ir::ICmpOp::Ule => {}
            trust_ir::ICmpOp::Ugt => {}
            trust_ir::ICmpOp::Uge => {}
            trust_ir::ICmpOp::Slt => {}
            trust_ir::ICmpOp::Sle => {}
            trust_ir::ICmpOp::Sgt => {}
            trust_ir::ICmpOp::Sge => {}
        }
        match overflowop_value {
            trust_ir::OverflowOp::AddOverflow => {}
            trust_ir::OverflowOp::SubOverflow => {}
            trust_ir::OverflowOp::MulOverflow => {}
        }
        match castop_value {
            trust_ir::CastOp::Trunc => {}
            trust_ir::CastOp::ZExt => {}
            trust_ir::CastOp::SExt => {}
            trust_ir::CastOp::FPTrunc => {}
            trust_ir::CastOp::FPExt => {}
            trust_ir::CastOp::FPToUI => {}
            trust_ir::CastOp::FPToSI => {}
            trust_ir::CastOp::UIToFP => {}
            trust_ir::CastOp::SIToFP => {}
            trust_ir::CastOp::PtrToInt => {}
            trust_ir::CastOp::IntToPtr => {}
            trust_ir::CastOp::PtrToPtr => {}
            trust_ir::CastOp::Bitcast => {}
            trust_ir::CastOp::Transmute => {}
            trust_ir::CastOp::ReifyFnPointer => {}
            trust_ir::CastOp::FPToSISat => {}
            trust_ir::CastOp::FPToUISat => {}
        }
        let trust_ir::StorageLayout {
            size_bytes: _,
            align_bytes: _,
        } = storage_value;
        let trust_ir::ClosureTy {
            func: _,
            captures: _,
        } = closurety_value;
        let trust_ir::FuncTy {
            params: _,
            returns: _,
            is_vararg: _,
            abi: _,
        } = functy_value;
        let trust_ir::SwitchCase {
            value: _,
            target: _,
            args: _,
        } = switchcase_value;
        let trust_ir::SourceSpan {
            file: _,
            line: _,
            col: _,
        } = sourcespan_value;
        let trust_ir::ProofLineageNode {
            id: _,
            transform: _,
            source_module: _,
            target_module: _,
            obligations: _,
            certificates: _,
            replay: _,
            depends_on: _,
        } = prooflineagenode_value;
        let trust_ir::ProofCertificateRef {
            obligation: _,
            prover: _,
            evidence_digest: _,
        } = proofcertificateref_value;
        let trust_ir::proof::ProofReplayIdentity {
            engine: _,
            invocation: _,
            transcript_digest: _,
        } = proofreplayidentity_value;
        let trust_ir::request::NativeRequestProvenance {
            verifier_suite: _,
            expected_verifier: _,
            solvers: _,
            replay: _,
            replay_context: _,
        } = nativerequestprovenance_value;
        let trust_ir::request::NativeEvidenceArtifact {
            name: _,
            kind: _,
            digest: _,
        } = nativeevidenceartifact_value;
        let trust_ir::request::NativeToolIdentity {
            name: _,
            version: _,
            revision: _,
            digest: _,
        } = nativetoolidentity_value;
        let trust_ir::request::TrustVcNativeEvidenceBundle {
            request: _,
            mode: _,
            obligations: _,
            verifier: _,
            solvers: _,
            replay: _,
            trust_ir_module_digest: _,
            request_digest: _,
            artifacts: _,
        } = trustvcnativeevidencebundle_value;
        let trust_ir::ProofDigest {
            algorithm: _,
            bytes: _,
        } = proofdigest_value;
        let trust_ir::ValueId(_) = valueid_value;
        let trust_ir::BlockId(_) = blockid_value;
        let trust_ir::FuncId(_) = funcid_value;
        let trust_ir::FuncTyId(_) = functyid_value;
        let trust_ir::TyId(_) = tyid_value;
        let trust_ir::ProofId(_) = proofid_value;
        let trust_ir::ProofLineageId(_) = prooflineageid_value;
        let trust_ir::request::NativeAssertionId(_) = nativeassertionid_value;
        let trust_ir::request::NativeReplayContext {
            atoms: _,
            unsupported_modes: _,
        } = nativereplaycontext_value;
        let trust_ir::request::NativeReplayAtom {
            id: _,
            kind: _,
            formula: _,
            payload_digest: _,
            obligation: _,
            assertion_id: _,
            span: _,
        } = nativereplayatom_value;
        match nativereplayatomkind_value {
            trust_ir::request::NativeReplayAtomKind::Assumption
            | trust_ir::request::NativeReplayAtomKind::Assertion => {}
        }
        let trust_ir::request::NativeReplayAtomId(_) = nativereplayatomid_value;
        // MERGED 2026-09-23: witnesses for the types upstream's ADVISORY body
        // lane names. `Interpreter` has private fields and cannot be
        // destructured; its entry in `UNTABLED_PRODUCER_TYPES` says so.
        let trust_ir::InterpretOptions {
            fuel: _,
            max_call_depth: _,
            panic_strategy: _,
        } = interpretoptions_value;
        let trust_ir::InterpretValue { ty: _, kind: _ } = interpretvalue_value;
        match interpreterrorcode_value {
            trust_ir::InterpretErrorCode::UnsupportedDialectOp
            | trust_ir::InterpretErrorCode::UnsupportedCall
            | trust_ir::InterpretErrorCode::UnsupportedMemory
            | trust_ir::InterpretErrorCode::UnsupportedVectorShape
            | trust_ir::InterpretErrorCode::UnsupportedInstruction
            | trust_ir::InterpretErrorCode::UnsupportedCast
            | trust_ir::InterpretErrorCode::UnsupportedFloat
            | trust_ir::InterpretErrorCode::TypeError
            | trust_ir::InterpretErrorCode::UndefinedBehavior
            | trust_ir::InterpretErrorCode::Panic
            | trust_ir::InterpretErrorCode::OutOfFuel
            | trust_ir::InterpretErrorCode::OutOfMemory
            | trust_ir::InterpretErrorCode::MissingFunction
            | trust_ir::InterpretErrorCode::InvalidFunctionPointer
            | trust_ir::InterpretErrorCode::SignatureMismatch
            | trust_ir::InterpretErrorCode::MissingBlock
            | trust_ir::InterpretErrorCode::MissingValue
            | trust_ir::InterpretErrorCode::MalformedInstruction
            | trust_ir::InterpretErrorCode::AssumeViolated => {}
        }
        let trust_ir::FuncAttrs {
            readonly: _,
            readnone: _,
            inlinehint: _,
            cold: _,
            params: _,
            naked: _,
            target_features: _,
            ret: _,
        } = funcattrs_value;
        match linkage_value {
            trust_ir::Linkage::External
            | trust_ir::Linkage::Internal
            | trust_ir::Linkage::Private
            | trust_ir::Linkage::Weak
            | trust_ir::Linkage::LinkOnce
            | trust_ir::Linkage::AvailableExternally
            | trust_ir::Linkage::ExternalWeak
            | trust_ir::Linkage::WeakOdr
            | trust_ir::Linkage::LinkOnceOdr => {}
        }
        match proofdigestalgorithm_value {
            trust_ir::ProofDigestAlgorithm::Sha256
            | trust_ir::ProofDigestAlgorithm::TrustIrStableV1 => {}
        }
        let trust_ir::proof::CoverageAssurance {
            bound: _,
            request_digest: _,
        } = coverageassurance_value;
        match coveragebound_value {
            trust_ir::proof::CoverageBound::Unbounded
            | trust_ir::proof::CoverageBound::UnwindBounded { depth: _ }
            | trust_ir::proof::CoverageBound::ModelBounded { size: _ }
            | trust_ir::proof::CoverageBound::Unrecorded => {}
            // `#[non_exhaustive]`, so the wildcard is forced and a new bound
            // reaches this crate silently. `judge_certificate` matches only
            // `Unbounded` and refuses every other bound through its own
            // catch-all arm, so an unnamed bound is refused, never admitted.
            _ => {}
        }
        let trust_ir::proof::SpecObligationRef {
            machine: _,
            temporal: _,
        } = specobligationref_value;
        match trustmcverificationmode_value {
            trust_ir::request::TrustMcVerificationMode::BoundedModelCheck
            | trust_ir::request::TrustMcVerificationMode::Chc
            | trust_ir::request::TrustMcVerificationMode::Pdr => {}
        }
        match trustwpverificationmode_value {
            trust_ir::request::TrustWpVerificationMode::WeakestPrecondition
            | trust_ir::request::TrustWpVerificationMode::StrongestPostcondition
            | trust_ir::request::TrustWpVerificationMode::Abduction => {}
        }
        match trustwpframepolicy_value {
            trust_ir::request::TrustWpFramePolicy::Minimal
            | trust_ir::request::TrustWpFramePolicy::BorrowRegions
            | trust_ir::request::TrustWpFramePolicy::FullHeap => {}
        }
        match trustwploopstrategy_value {
            trust_ir::request::TrustWpLoopStrategy::RequireInvariants
            | trust_ir::request::TrustWpLoopStrategy::InferInvariants
            | trust_ir::request::TrustWpLoopStrategy::Havoc => {}
        }
        match visibility_value {
            trust_ir::Visibility::Default
            | trust_ir::Visibility::Hidden
            | trust_ir::Visibility::Protected => {}
        }
        // The coverage verdict `native_coverage.rs` reads. The report itself
        // (`CoverageEstablishmentReport`) has private fields and cannot be
        // destructured; its entry in `UNTABLED_PRODUCER_TYPES` says so.
        let trust_ir_build::CoverageInputs {
            attestation: _,
            solved_bundles: _,
            attachments: _,
            replay: _,
        } = coverageinputs_value;
        match certificatecoverage_value {
            trust_ir_build::CertificateCoverage::Established { bound: _, basis: _ }
            | trust_ir_build::CertificateCoverage::Undetermined { reason: _ }
            | trust_ir_build::CertificateCoverage::Refused(_) => {}
        }
        match coveragebasis_value {
            trust_ir_build::CoverageBasis::KernelReplayedClaim {
                certificate: _,
                family: _,
            } => {}
            // `#[non_exhaustive]`, so the wildcard is forced. `judge_certificate`
            // accepts only `KernelReplayedClaim` naming the judged certificate;
            // any other basis is refused.
            _ => {}
        }
        match coverageundeterminedreason_value {
            trust_ir_build::CoverageUndeterminedReason::ReportUnchecked
            | trust_ir_build::CoverageUndeterminedReason::CertificateNotInModule
            | trust_ir_build::CoverageUndeterminedReason::ObligationNotInModule
            | trust_ir_build::CoverageUndeterminedReason::NoBasis
            | trust_ir_build::CoverageUndeterminedReason::KernelUnavailable
            | trust_ir_build::CoverageUndeterminedReason::ClaimFamilyUnclassified
            | trust_ir_build::CoverageUndeterminedReason::NotTheReplayedCertificate
            | trust_ir_build::CoverageUndeterminedReason::NoReplayer
            | trust_ir_build::CoverageUndeterminedReason::ReplayInconclusive {
                reason: _,
                detail: _,
            }
            | trust_ir_build::CoverageUndeterminedReason::ObligationNotModeled
            | trust_ir_build::CoverageUndeterminedReason::RequestNotMachineSemantics {
                divergence: _,
            }
            | trust_ir_build::CoverageUndeterminedReason::GoalAnnotationUnbound { function: _ }
            | trust_ir_build::CoverageUndeterminedReason::PremiseNotEstablished { premise: _ } => {}
            // `#[non_exhaustive]`: every reason, named or not, leaves the
            // certificate undetermined, which rejects it.
            _ => {}
        }
        match kernelclaimfamily_value {
            trust_ir::proof::KernelClaimFamily::ContractGroundDecision => {}
            // `#[non_exhaustive]`: `kernel_claim_family` classifies only
            // `ContractGroundDecision`, so any other family is undetermined.
            _ => {}
        }
        match dropresolution_value {
            trust_ir::DropResolution::Resolved(_)
            | trust_ir::DropResolution::Unresolved
            | trust_ir::DropResolution::Ambiguous => {}
        }
        match boxpointee_value {
            trust_ir::box_validity::BoxPointee::Sized { ty: _ } => {}
        }
        let trust_ir::box_validity::BoxValidityFact {
            site: _,
            session: _,
            evidence: _,
            not_claimed: _,
        } = boxvalidityfact_value;
        let trust_ir::box_validity::BoxDerefSite {
            item: _,
            ordinal: _,
        } = boxderefsite_value;
        let trust_ir::box_validity::BoxFactSession {
            judged: _,
            producing: _,
        } = boxfactsession_value;
        match premiseroot_value {
            trust_ir::box_validity::PremiseRoot::ParamByValue
            | trust_ir::box_validity::PremiseRoot::AllocPostcondition
            | trust_ir::box_validity::PremiseRoot::ReturnedBoxDischarged
            | trust_ir::box_validity::PremiseRoot::ReturnedBoxAssumed
            | trust_ir::box_validity::PremiseRoot::ReferenceArgBoxValid => {}
        }
        vec![
            "BoxPointee",
            "BoxValidityFact",
            "BoxDerefSite",
            "BoxFactSession",
            "PremiseRoot",
            "Inst",
            "Ty",
            "Constant",
            "ProofEvidence",
            "NativeVerificationBundleError",
            "NativeCompilerFactRef",
            "NativeAdapterInput",
            "NativeVerificationRequest",
            "ObligationKind",
            "ProofStatus",
            "NativeObligationCause",
            "TrustVcVerificationMode",
            "NativeVerifierSuite",
            "NativeEvidenceArtifactKind",
            "NativeBundleProducer",
            "CallingConv",
            "Endianness",
            "StructPassingPolicy",
            "BinOp",
            "UnOp",
            "ICmpOp",
            "OverflowOp",
            "CastOp",
            "FuncTy",
            "ClosureTy",
            "StorageLayout",
            "SwitchCase",
            "SourceSpan",
            "ProofLineageNode",
            "ProofCertificateRef",
            "ProofReplayIdentity",
            "NativeRequestProvenance",
            "NativeEvidenceArtifact",
            "NativeToolIdentity",
            "TrustVcNativeEvidenceBundle",
            "ProofDigest",
            "ValueId",
            "BlockId",
            "FuncId",
            "FuncTyId",
            "TyId",
            "ProofId",
            "ProofLineageId",
            "NativeAssertionId",
            "NativeReplayContext",
            "NativeReplayAtom",
            "NativeReplayAtomKind",
            "NativeReplayAtomId",
            "InterpretOptions",
            "InterpretValue",
            "InterpretErrorCode",
            "FuncAttrs",
            "Linkage",
            "ProofDigestAlgorithm",
            "CoverageAssurance",
            "CoverageBound",
            "SpecObligationRef",
            "TrustMcVerificationMode",
            "TrustWpVerificationMode",
            "TrustWpFramePolicy",
            "TrustWpLoopStrategy",
            "Visibility",
            "CoverageInputs",
            "CertificateCoverage",
            "CoverageBasis",
            "CoverageUndeterminedReason",
            "KernelClaimFamily",
            "DropResolution",
        ]
    }

    /// The two compile-time ratchets, the table and the exclusions name EXACTLY
    /// the same set of producer types.
    ///
    /// A type may be in the table (every field or variant enumerated, with a
    /// note) or in [`UNTABLED_PRODUCER_TYPES`] (with a reason), never in both
    /// and never in neither.
    #[test]
    fn the_table_and_the_exclusions_cover_exactly_the_types_the_ratchets_pin() {
        // Never called: they exist to be TYPE-CHECKED. Referencing them here
        // keeps them from being dead code.
        #[allow(unused)]
        let covered = producer_types_are_exhaustively_enumerated;
        #[allow(unused)]
        let covered_values = producer_value_types_are_exhaustively_enumerated;
        let pinned: BTreeSet<&str> = PINNED_PRODUCER_TYPES.iter().copied().collect();
        let tabled: BTreeSet<&str> = PRODUCER_FIELDS.iter().map(|row| row.ty).collect();
        let excluded: BTreeSet<&str> = UNTABLED_PRODUCER_TYPES
            .iter()
            .map(|excluded| excluded.ty)
            .collect();
        assert!(
            tabled.is_disjoint(&excluded),
            "a type may be tabled or excluded, not both: {:?}",
            tabled.intersection(&excluded).collect::<Vec<_>>()
        );
        let covered: BTreeSet<&str> = tabled.union(&excluded).copied().collect();
        assert_eq!(covered, pinned);
        for excluded in UNTABLED_PRODUCER_TYPES {
            assert!(
                !excluded.reason.is_empty(),
                "`{}` is excluded with no reason",
                excluded.ty
            );
        }
    }

    /// THE CLOSURE RATCHET — the answer to round 9's major.
    ///
    /// The type list above is still written by a person, so this test derives
    /// the set of `trust_ir` types this crate NAMES from the crate's own sources
    /// and requires every one of them to be tabled or explicitly excluded.
    /// Reaching for a new producer type — in any file, for any purpose — fails
    /// here until someone says what the lane does with it.
    ///
    /// The derivation is deliberately crude and OVER-approximating: every
    /// capitalised identifier inside a `use <producer crate>::...;` statement,
    /// plus every `<producer crate>::..::Type` path, in comment- and
    /// string-stripped code. An over-approximation can only demand MORE
    /// dispositions, never fewer.
    ///
    /// ROUND 11's FIRST CENSUS GAP. This scanned `trust_ir::` and nothing else,
    /// so the PRODUCER'S VALIDATOR CRATE was entirely outside the census: probe
    /// R10-P5 added a function reading
    /// `trust_ir_build::ValidationError::EmptyFunction` and
    /// `::DischargedWithoutCertificate` and every census test passed. The token
    /// `trust_ir_build::` does not contain `trust_ir::`, so no amount of
    /// scanning the latter could ever have found it — and `ValidationError` is
    /// decision-bearing here: `is_proof_replay_capability_verdict` destructures
    /// one of its variants to carry an upstream refusal PAST the input gate.
    /// Every producer crate this lane names is now scanned.
    #[test]
    fn every_trust_ir_type_this_crate_names_is_tabled_or_excluded() {
        let sources = crate_sources();
        let mut named: BTreeSet<String> = BTreeSet::new();
        for text in sources.values() {
            for producer_crate in PRODUCER_CRATES {
                let import = format!("use {producer_crate}::");
                for start in find_all(text, &import) {
                    let Some(end) = text[start..].find(';') else {
                        continue;
                    };
                    for word in words(&text[start..start + end]) {
                        if starts_upper(&word) {
                            named.insert(word);
                        }
                    }
                }
                let prefix = format!("{producer_crate}::");
                for start in find_all(text, &prefix) {
                    // `trust_ir::` is a prefix of nothing else here, but
                    // `trust_ir_build::` proves the general point: a path token
                    // must not be matched as the tail of a longer identifier.
                    let bytes = text.as_bytes();
                    if start > 0
                        && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
                    {
                        continue;
                    }
                    let mut rest = &text[start + prefix.len()..];
                    loop {
                        let word = leading_word(rest);
                        if word.is_empty() {
                            break;
                        }
                        if starts_upper(&word) {
                            named.insert(word);
                            break;
                        }
                        rest = &rest[word.len()..];
                        if rest.starts_with("::") {
                            rest = &rest[2..];
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        assert!(
            named.len() > 40,
            "the derivation found only {} type names, which cannot be right: {named:?}",
            named.len()
        );

        let pinned: BTreeSet<&str> = PINNED_PRODUCER_TYPES.iter().copied().collect();
        let missing: Vec<&String> = named
            .iter()
            .filter(|name| !pinned.contains(name.as_str()))
            .collect();
        assert!(
            missing.is_empty(),
            "these producer types are named by this crate but are neither tabled in \
             PRODUCER_FIELDS nor listed in UNTABLED_PRODUCER_TYPES with a reason. Do not add \
             them to the exclusions to make this pass: enumerate the type's fields, measure \
             what this crate reads, and write down whether the lane's invariant holds \
             there.\n{missing:?}"
        );
    }

    /// THE VARIANT-PATH RATCHET — the other half of round 11's first census gap.
    ///
    /// The closure ratchet above pins the TYPE. This pins the VARIANT: every
    /// `Type::Variant` path this crate's code names, for any pinned producer
    /// type, must have a row. Round 8's read-site scan already keys enum rows by
    /// that path, but only for variants someone had already tabled — so reaching
    /// for a NEW variant of an enum was free. Probe R10-P5 did exactly that with
    /// `ValidationError::EmptyFunction`.
    ///
    /// This is the only ratchet `ValidationError` can have: it is
    /// `#[non_exhaustive]` upstream with about a hundred variants, so the
    /// compile-time exhaustive destructure that pins every other producer enum
    /// is impossible for it. What still pins the variants this crate DOES use is
    /// the compiler: `ValidationError::DischargedWithoutCertificate { .. }` is
    /// written as a pattern, so removing or reshaping it upstream breaks the
    /// build.
    #[test]
    fn every_producer_named_path_this_crate_names_is_tabled() {
        let sources = crate_sources();
        let tabled: BTreeSet<String> = PRODUCER_FIELDS
            .iter()
            .filter(|row| row.kind == ProducerFieldKind::NamedPath)
            .map(|row| format!("{}::{}", row.ty, row.field))
            .collect();

        // ROUND 12: every SPELLING of each pinned type, so a local `type` alias
        // cannot rename its way out of the scan. The variant is reported under
        // the type's real name whichever spelling named it.
        let spellings = producer_type_spellings();
        let mut untabled: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (path, text) in &sources {
            let bytes = text.as_bytes();
            for (ty, spellings) in &spellings {
                for spelling in spellings {
                    let prefix = format!("{spelling}::");
                    for start in find_all(text, &prefix) {
                        if start > 0
                            && (bytes[start - 1].is_ascii_alphanumeric()
                                || bytes[start - 1] == b'_')
                        {
                            continue;
                        }
                        let word = leading_word(&text[start + prefix.len()..]);
                        // Lowercase tails are associated functions
                        // (`ProofId::new`), not variants.
                        if word.is_empty() || !starts_upper(&word) {
                            continue;
                        }
                        let named = format!("{ty}::{word}");
                        if !tabled.contains(&named) {
                            untabled.entry(named).or_default().insert(path.clone());
                        }
                    }
                }
            }
        }
        assert!(
            untabled.is_empty(),
            "these producer enum VARIANTS are named by this crate's code but have no row. Do \
             not delete the read to make this pass, and do not add a row without reading the \
             site: say what the lane does with the variant, then record it.\n{untabled:?}"
        );
    }

    fn starts_upper(word: &str) -> bool {
        word.chars().next().is_some_and(char::is_uppercase)
    }

    fn leading_word(text: &str) -> String {
        text.chars()
            .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
            .collect()
    }

    fn words(text: &str) -> Vec<String> {
        let mut out = Vec::new();
        let mut current = String::new();
        for ch in text.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                current.push(ch);
            } else if !current.is_empty() {
                out.push(std::mem::take(&mut current));
            }
        }
        if !current.is_empty() {
            out.push(current);
        }
        out
    }

    fn find_all(text: &str, needle: &str) -> Vec<usize> {
        let mut out = Vec::new();
        let mut from = 0usize;
        while let Some(found) = text[from..].find(needle) {
            out.push(from + found);
            from += found + 1;
        }
        out
    }

    /// EVERY source file in the crate, comments and string literals blanked out
    /// — the table's own file included.
    ///
    /// Only the ALIAS scan reads this: a `type` alias declared in the table's
    /// own file and used elsewhere would otherwise be invisible, which is the
    /// third evasion one file over.
    fn all_crate_sources() -> BTreeMap<String, String> {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut sources: BTreeMap<String, String> = BTreeMap::new();
        collect_rust_sources(&root, &root, &mut sources);
        assert!(
            sources.len() > 5,
            "the scan found only {} source files",
            sources.len()
        );
        sources
    }

    /// The crate's own sources with the STRING LITERALS KEPT (comments still
    /// blanked), for the string-key scan — the table's own file excluded, as
    /// everywhere else, because it spells every producer field name in a string
    /// by construction.
    fn crate_sources_with_string_literals() -> BTreeMap<String, String> {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut sources: BTreeMap<String, String> = BTreeMap::new();
        collect_rust_sources_with(&root, &root, &mut sources, strip_comments);
        sources.remove("producer_fields.rs");
        assert!(
            sources.len() > 5,
            "the scan found only {} source files",
            sources.len()
        );
        sources
    }

    /// The crate's own sources, comments and string literals blanked out.
    fn crate_sources() -> BTreeMap<String, String> {
        let mut sources = all_crate_sources();
        // THIS file is the table, not a consumer of the wire format: it names
        // every producer type and field by construction, and its own scaffolding
        // would match every scan. It is excluded so the ratchets measure the
        // CRATE and not themselves.
        sources.remove("producer_fields.rs");
        sources
    }

    /// EVERY SPELLING OF A PRODUCER TYPE IN THIS CRATE — round 12's closure of
    /// the THIRD EVASION.
    ///
    /// Every path-keyed scan here matches a SPELLING (`NativeObligationSource::`,
    /// `ValidationError` followed by a brace). A one-line local alias renames a
    /// producer type and all of them go blind at once. MEASURED (round 11's
    /// review, evasion 3):
    ///
    /// ```text
    /// type ZzVe = trust_ir_build::ValidationError;
    /// pub(crate) fn zz_e3a(error: &ZzVe) -> u8 {
    ///     match error { ZzVe::EmptyFunction { .. } => 1, _ => 0 }
    /// }
    /// ```
    ///
    /// passed all five census tests, while the same read spelled
    /// `trust_ir_build::ValidationError::EmptyFunction` failed two. The alias is
    /// not a `use` statement, so the closure ratchet's use-scan never saw it
    /// either: the capability R10-P5 demonstrated survived the ratchet that was
    /// added to close it.
    ///
    /// Aliases are RESOLVED, not banned. A `type A = ...;` or a `use ... as A;`
    /// whose right-hand side names a pinned producer type — or an alias of one,
    /// chased to a fixpoint — makes `A` a second spelling of that type, and
    /// every scan below reads both spellings. Deliberately OVER-approximating,
    /// like the rest of this module: `type A = Option<NativeObligationSource>;`
    /// counts as a spelling of `NativeObligationSource`, which can only demand
    /// more dispositions, never fewer.
    fn producer_type_spellings() -> BTreeMap<String, BTreeSet<String>> {
        let sources = all_crate_sources();
        let pinned: BTreeSet<&str> = PINNED_PRODUCER_TYPES.iter().copied().collect();
        let candidates = alias_candidates(sources.values());
        let aliases = resolve_alias_candidates(&candidates, &pinned);

        let mut spellings: BTreeMap<String, BTreeSet<String>> = PINNED_PRODUCER_TYPES
            .iter()
            .map(|ty| ((*ty).to_string(), BTreeSet::from([(*ty).to_string()])))
            .collect();
        for (alias, ty) in aliases {
            spellings.entry(ty).or_default().insert(alias);
        }
        spellings
    }

    /// Every `(alias, right-hand side)` pair the sources declare.
    ///
    /// Split out of [`producer_type_spellings`] at ROUND 13 so the scan can be
    /// measured on synthetic text — the reviewer's two-hop probe lives in the
    /// test below rather than only in a source file that has to be deleted.
    fn alias_candidates<'a>(
        sources: impl IntoIterator<Item = &'a String>,
    ) -> Vec<(String, String)> {
        let mut candidates: Vec<(String, String)> = Vec::new();
        for text in sources {
            let bytes = text.as_bytes();
            // `type A = <rhs>;`
            for start in find_all(text, "type ") {
                if start > 0
                    && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
                {
                    continue;
                }
                let rest = &text[start + "type ".len()..];
                let Some(end) = rest.find(';') else { continue };
                let statement = &rest[..end];
                let Some(equals) = statement.find('=') else {
                    continue;
                };
                let alias = leading_word(statement.trim_start());
                if alias.is_empty() || !starts_upper(&alias) {
                    continue;
                }
                candidates.push((alias, statement[equals + 1..].to_string()));
            }
            // `use <producer crate>::<path> as A;`, and — ROUND 13 — a
            // `use self::/crate::/super::<path> as A;` that renames an alias a
            // second time. The FOREIGN root must be a producer crate: this
            // crate imports `trust_vc_core::vc::ObligationKind as
            // TrustVcObligationKind`, and that is a DIFFERENT type that happens
            // to share a name with `trust_ir::ObligationKind` (measured — the
            // first cut of this scan reported twelve of its variants as
            // untabled producer reads). A LOCAL root cannot name another
            // crate's type at all, so admitting it costs nothing and closes the
            // `use self::Alias as Alias2;` spelling of round 13's two-hop
            // evasion.
            for start in find_all(text, "use ") {
                if start > 0
                    && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
                {
                    continue;
                }
                let rest = &text[start + "use ".len()..];
                let Some(end) = rest.find(';') else { continue };
                let statement = rest[..end].trim_start();
                let root = leading_word(statement);
                if !PRODUCER_CRATES.contains(&root.as_str())
                    && !LOCAL_PATH_ROOTS.contains(&root.as_str())
                {
                    continue;
                }
                let mut segments = statement.split(" as ");
                let mut left = segments.next().unwrap_or_default().to_string();
                for right in segments {
                    let alias = leading_word(right.trim_start());
                    if !alias.is_empty() && starts_upper(&alias) {
                        if let Some(target) = words(&left).pop() {
                            candidates.push((alias, target));
                        }
                    }
                    left = right.to_string();
                }
            }
        }

        candidates
    }

    /// Chase alias -> alias to a fixpoint. The bound is the candidate count:
    /// one round resolves at least one new alias, or nothing changes.
    fn resolve_alias_candidates(
        candidates: &[(String, String)],
        pinned: &BTreeSet<&str>,
    ) -> BTreeMap<String, String> {
        let mut aliases: BTreeMap<String, String> = BTreeMap::new();
        for _ in 0..=candidates.len() {
            let mut changed = false;
            for (alias, target) in candidates {
                if aliases.contains_key(alias) || pinned.contains(alias.as_str()) {
                    continue;
                }
                if let Some(resolved) = resolve_producer_type(target, pinned, &aliases) {
                    aliases.insert(alias.clone(), resolved);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        aliases
    }

    /// ROUND 13's THIRD CENSUS EVASION, PINNED — the two-hop alias.
    ///
    /// The reviewer's probe, verbatim, run against the scan instead of against
    /// a source file that has to be deleted afterwards:
    ///
    /// ```text
    /// type R12Ve  = trust_ir_build::ValidationError;
    /// type R12Ve2 = self::R12Ve;
    /// ```
    ///
    /// MEASURED before the fix: the two-hop form passed ALL SIX census tests
    /// while the same probe with the second hop removed failed three, so the
    /// second hop alone was the evasion. `resolve_producer_type` gave up on any
    /// right-hand side containing `::`, and the `use` scan required the path
    /// ROOT to be a producer crate, so `self::`/`crate::`/`super::` resolved to
    /// nothing.
    ///
    /// The REFUTED TWIN is the second half and matters as much: a path rooted
    /// in a FOREIGN crate whose last segment is a pinned NAME must still
    /// resolve to nothing. `trust_vc_core::vc::ObligationKind` is not
    /// `trust_ir::ObligationKind`, and reading it as one reported twelve false
    /// producer reads when the scan was first cut.
    #[test]
    fn a_two_hop_alias_resolves_and_a_foreign_rooted_pinned_tail_does_not() {
        let pinned: BTreeSet<&str> = PINNED_PRODUCER_TYPES.iter().copied().collect();
        let resolve = |text: &str| {
            let source = text.to_string();
            resolve_alias_candidates(&alias_candidates(std::iter::once(&source)), &pinned)
        };

        // VERIFIED: both hops, in every local spelling, land on the real type.
        let aliases = resolve(
            "type R12Ve = trust_ir_build::ValidationError;\n\
             type R12Ve2 = self::R12Ve;\n\
             type R12Ve3 = crate::probe::R12Ve2;\n\
             use self::R12Ve3 as R12Ve4;\n\
             type R12Nos = trust_ir::NativeObligationSource;\n\
             type R12Nos2 = super::probe::R12Nos;\n",
        );
        for alias in ["R12Ve", "R12Ve2", "R12Ve3", "R12Ve4"] {
            assert_eq!(
                aliases.get(alias).map(String::as_str),
                Some("ValidationError"),
                "`{alias}` is a spelling of `ValidationError` and the scan must say so: \
                 {aliases:?}"
            );
        }
        for alias in ["R12Nos", "R12Nos2"] {
            assert_eq!(
                aliases.get(alias).map(String::as_str),
                Some("NativeObligationSource"),
                "`{alias}` is a spelling of `NativeObligationSource`: {aliases:?}"
            );
        }

        // REFUTED: a foreign root is not this producer, however the tail reads,
        // and neither is an alias chain built on one.
        let foreign = resolve(
            "type R13Ok = trust_vc_core::vc::ObligationKind;\n\
             type R13Ok2 = self::R13Ok;\n\
             use self::R13Ok2 as R13Ok3;\n",
        );
        assert!(
            foreign.is_empty(),
            "`trust_vc_core::vc::ObligationKind` is a DIFFERENT type that shares a name with \
             `trust_ir::ObligationKind`; resolving it as a producer spelling reports twelve \
             false producer reads: {foreign:?}"
        );

        // REFUTED: an unrelated bare alias resolves to nothing, so the scan is
        // not simply answering "yes" to everything.
        assert!(resolve("type R13Zz = std::string::String;\n").is_empty());
    }

    /// Which pinned producer type, if any, an alias's right-hand side names.
    ///
    /// A path ROOTED IN A PRODUCER CRATE resolves to the first capitalised
    /// segment after the crate — the same walk the closure ratchet does. A path
    /// rooted in any OTHER crate resolves to nothing by its tail, however
    /// familiar that tail reads: `trust_vc_core::vc::ObligationKind` is not
    /// `trust_ir`'s. A right-hand side with no path at all falls back to a bare
    /// name, which is the spelling an in-scope `use` of a producer type has.
    ///
    /// ROUND 13 added the remaining case: any path, whatever its root, has its
    /// SEGMENTS resolved against the alias map, and a LOCAL root
    /// ([`LOCAL_PATH_ROOTS`]) additionally admits a pinned tail. That is the
    /// two-hop evasion, closed — see the test above for the probe and its
    /// refuted twin.
    fn resolve_producer_type(
        rhs: &str,
        pinned: &BTreeSet<&str>,
        aliases: &BTreeMap<String, String>,
    ) -> Option<String> {
        for producer_crate in PRODUCER_CRATES {
            let prefix = format!("{producer_crate}::");
            let bytes = rhs.as_bytes();
            for start in find_all(rhs, &prefix) {
                if start > 0
                    && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
                {
                    continue;
                }
                let mut rest = &rhs[start + prefix.len()..];
                loop {
                    let word = leading_word(rest);
                    if word.is_empty() {
                        break;
                    }
                    if starts_upper(&word) {
                        return pinned.contains(word.as_str()).then_some(word);
                    }
                    rest = &rest[word.len()..];
                    if rest.starts_with("::") {
                        rest = &rest[2..];
                    } else {
                        break;
                    }
                }
            }
        }
        if rhs.contains("::") {
            // ROUND 13's THIRD CENSUS EVASION — A TWO-HOP ALIAS.
            //
            // Returning `None` here was right about the ROOT and wrong about
            // the TAIL. A path root outside PRODUCER_CRATES does not name a
            // producer type, but a SEGMENT of that path can still be an ALIAS
            // of one, and `self::`/`crate::`/`super::` are exactly the roots a
            // local alias is reachable through. MEASURED (round 12's review,
            // evasion 3):
            //
            // ```text
            // type R12Ve  = trust_ir_build::ValidationError;
            // type R12Ve2 = self::R12Ve;              // <- invisible before
            // match error { R12Ve2::EmptyFunction => .. }
            // ```
            //
            // The first hop resolved; the second did not, so `R12Ve2` was not a
            // spelling of anything and ALL SIX census tests passed. The same
            // probe with the second hop removed failed three of them, so the
            // second hop alone was the evasion.
            //
            // Segments are resolved against the ALIAS MAP, never against
            // `pinned`, whatever the root — that is the deliberate bare-name
            // keying this module has carried since round 12, and it is what
            // keeps `trust_vc_core::vc::ObligationKind` (whose LAST SEGMENT is
            // a pinned name and whose type is not this producer's) out of the
            // census. The one exception is a LOCAL root: `self::X` cannot name
            // another crate's `X`, so a pinned tail under a local root is this
            // producer's type and is admitted. Scanning every segment rather
            // than only the last is the usual over-approximation — it can only
            // demand more dispositions, never fewer.
            let local = LOCAL_PATH_ROOTS.iter().any(|root| {
                let token = format!("{root}::");
                let bytes = rhs.as_bytes();
                find_all(rhs, &token).into_iter().any(|start| {
                    start == 0
                        || !(bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
                })
            });
            for word in words(rhs) {
                if let Some(resolved) = aliases.get(&word) {
                    return Some(resolved.clone());
                }
                if local && pinned.contains(word.as_str()) {
                    return Some(word);
                }
            }
            return None;
        }
        words(rhs).into_iter().find_map(|word| {
            if pinned.contains(word.as_str()) {
                Some(word)
            } else {
                aliases.get(&word).cloned()
            }
        })
    }

    /// THE CRATE HALF OF THE RATCHET.
    ///
    /// Re-derives every read site from this crate's own sources and compares it
    /// to the table. A producer field that gains a read site in a file the table
    /// does not list FAILS HERE — which is worth more than the table, because
    /// the table is what went stale last time.
    ///
    /// Round 8's named gaps are all covered by construction:
    /// `NativeObligationSource::{assertion_id,function,span,cause,
    /// monomorphization,facts}`, `Function::{value_names,entry,blocks}` (the
    /// DISCHARGED function's, not only the callee's),
    /// `TrustVcNativeRequest::obligations`, and E20's correction —
    /// `ProofFormula::{sort,schema}` and `ProofObligation::description` are read
    /// by the CRATE (copied onto the evidence row) even though the LANE does not
    /// consult them.
    #[test]
    fn producer_field_read_sites_match_the_table() {
        let sources = crate_sources();

        // One field NAME may belong to several producer types; the scan cannot
        // tell them apart, so struct-field rows compare the UNION per name.
        // ENUM VARIANT rows are keyed by the full path `Type::Variant`, which is
        // exact.
        let mut expected: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
        for row in PRODUCER_FIELDS {
            let key = match row.kind {
                ProducerFieldKind::StructField => row.field.to_string(),
                ProducerFieldKind::NamedPath => format!("{}::{}", row.ty, row.field),
            };
            expected
                .entry(key)
                .or_default()
                .extend(row.read_sites.iter().copied());
        }

        // ROUND 12: an enum-variant row is keyed by `Type::Variant`, and the
        // scan must accept every SPELLING of the type — otherwise a local alias
        // hides a NEW read site of an ALREADY-TABLED variant, which is the third
        // evasion aimed at this scan instead of the variant ratchet (measured:
        // `type ZzVe2 = trust_ir_build::ValidationError;` in one file and
        // `ZzVe2::DischargedWithoutCertificate { .. }` in another passed all
        // five census tests).
        let spellings = producer_type_spellings();
        let mut drifted = Vec::new();
        for (field, recorded) in &expected {
            let observed: BTreeSet<String> = sources
                .iter()
                .filter(|(_, text)| match field.split_once("::") {
                    Some((ty, variant)) => spellings
                        .get(ty)
                        .map(|names| {
                            names
                                .iter()
                                .any(|name| mentions_path(text, &format!("{name}::{variant}")))
                        })
                        .unwrap_or_else(|| mentions_path(text, field)),
                    None => reads_field(text, field),
                })
                .map(|(path, _)| path.clone())
                .collect();
            // (`sources` holds CODE only — comments and string literals are
            // scrubbed by `strip_comments_and_strings` when the files are read.)
            let recorded: BTreeSet<String> =
                recorded.iter().map(|site| (*site).to_string()).collect();
            if observed != recorded {
                let added: Vec<&String> = observed.difference(&recorded).collect();
                let removed: Vec<&String> = recorded.difference(&observed).collect();
                drifted.push(format!(
                    "`{field}`: new read sites {added:?}, sites the table lists that no longer \
                     read it {removed:?}"
                ));
            }
        }
        assert!(
            drifted.is_empty(),
            "the derived producer-field table has drifted from the code. Do NOT widen the table \
             to make this pass: read each new site, decide whether the lane's invariant holds \
             there, write that in the row's `note`, and only then record the site.\n{}",
            drifted.join("\n")
        );
    }

    /// THE STRUCT-PATTERN RATCHET — the other half of round 9's correction,
    /// COUNTED as of round 11.
    ///
    /// A `Type { .. }` pattern reads fields without writing `.field`, so the
    /// field-access scan cannot see it. Every file that writes a brace after a
    /// producer struct's name is recorded, WITH HOW MANY it writes.
    ///
    /// ROUND 11's GAP. Until now this compared the SET of files, so a brace
    /// added to a file the table already listed was invisible — probe R10-P6
    /// added `let NativeObligationSource { span, facts, .. } = source` to
    /// `native_assertion_id.rs`, which the table already listed for that type,
    /// and all four census tests passed. Comparing counts closes it: the file
    /// went from one brace to two.
    #[test]
    fn producer_struct_brace_sites_match_the_table() {
        let sources = crate_sources();
        let tabled: BTreeSet<&str> = PRODUCER_FIELDS
            .iter()
            .filter(|row| row.kind == ProducerFieldKind::StructField)
            .map(|row| row.ty)
            .collect();
        let recorded_types: BTreeSet<&str> = PRODUCER_TYPE_BRACE_SITES
            .iter()
            .map(|entry| entry.ty)
            .collect();
        assert_eq!(
            tabled, recorded_types,
            "every producer STRUCT in the table needs a brace-site row"
        );

        // ROUND 12: count every SPELLING of the type, aliases included — see
        // `producer_type_spellings`.
        let spellings = producer_type_spellings();
        let mut drifted = Vec::new();
        for entry in PRODUCER_TYPE_BRACE_SITES {
            let names = spellings
                .get(entry.ty)
                .cloned()
                .unwrap_or_else(|| BTreeSet::from([entry.ty.to_string()]));
            let observed: BTreeMap<String, usize> = sources
                .iter()
                .map(|(path, text)| {
                    (
                        path.clone(),
                        names.iter().map(|name| count_braces(text, name)).sum(),
                    )
                })
                .filter(|(_, braces)| *braces > 0)
                .collect();
            let recorded: BTreeMap<String, usize> = entry
                .sites
                .iter()
                .map(|site| (site.file.to_string(), site.braces))
                .collect();
            if observed != recorded {
                let table = observed
                    .iter()
                    .map(|(file, braces)| {
                        format!("ProducerTypeBraceSite {{ file: \"{file}\", braces: {braces} }}")
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                drifted.push(format!(
                    "`{}`: recorded {recorded:?}, observed {observed:?}\n    sites: &[{table}],",
                    entry.ty
                ));
            }
        }
        assert!(
            drifted.is_empty(),
            "the producer-struct brace sites have drifted. A brace after a producer struct's \
             name is either a construction (fixture building) or a PATTERN that reads fields \
             the field-access scan cannot see. Read EVERY brace in the file whose count moved \
             — the new one may be a destructure the field-access scan cannot see — and only \
             then record the count.\n{}",
            drifted.join("\n")
        );
    }

    /// THE STRING-KEY RATCHET — round 12's closure of the fourth evasion.
    ///
    /// Every other scan here reads sources with the string literals blanked out,
    /// so a producer datum read through JSON (`value.get("monomorphization")`)
    /// is invisible to all of them. This one reads the same sources with the
    /// literals KEPT and counts, per file, every `get`/`get_mut`/index read of a
    /// string that spells a tabled producer field name. See
    /// [`PRODUCER_FIELD_STRING_KEY_SITES`] for what the recorded counts are and
    /// why they are a mixed bag.
    #[test]
    fn producer_field_string_key_sites_match_the_table() {
        let sources = crate_sources_with_string_literals();
        let fields: BTreeSet<&str> = PRODUCER_FIELDS
            .iter()
            .filter(|row| row.kind == ProducerFieldKind::StructField)
            .map(|row| row.field)
            .collect();

        let mut observed: BTreeMap<&str, BTreeMap<String, usize>> = BTreeMap::new();
        for field in &fields {
            for (path, text) in &sources {
                let reads = count_string_key_reads(text, field);
                if reads > 0 {
                    observed
                        .entry(field)
                        .or_default()
                        .insert(path.clone(), reads);
                }
            }
        }
        let recorded: BTreeMap<&str, BTreeMap<String, usize>> = PRODUCER_FIELD_STRING_KEY_SITES
            .iter()
            .map(|entry| {
                (
                    entry.field,
                    entry
                        .sites
                        .iter()
                        .map(|site| (site.file.to_string(), site.reads))
                        .collect(),
                )
            })
            .collect();

        if observed != recorded {
            let table = observed
                .iter()
                .map(|(field, sites)| {
                    let sites = sites
                        .iter()
                        .map(|(file, reads)| {
                            format!(
                                "ProducerFieldStringKeySite {{ file: \"{file}\", reads: {reads} }}"
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(
                        "ProducerFieldStringKeySites {{ field: \"{field}\", sites: &[{sites}] }},"
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            panic!(
                "the producer-field STRING KEY sites have drifted. A producer field read by \
                 string key has neither a field access nor a brace, so no other scan in this \
                 module can see it. Read every site whose count moved, say what the lane does \
                 with the datum, and only then record it.\nrecorded {recorded:?}\nobserved \
                 {observed:?}\n{table}"
            );
        }
    }

    /// How many times `text` reads `"<field>"` as a JSON key: `get("field")`,
    /// `get_mut("field")` or `["field"]`. WRITING a key (a `json!` literal, a
    /// `serde(rename)`) is a construction, not a read of a producer datum, and
    /// is deliberately not counted.
    fn count_string_key_reads(text: &str, field: &str) -> usize {
        let literal = format!("\"{field}\"");
        let bytes = text.as_bytes();
        let mut count = 0usize;
        for start in find_all(text, &literal) {
            let end = start + literal.len();
            let mut after = end;
            while after < bytes.len() && bytes[after].is_ascii_whitespace() {
                after += 1;
            }
            let mut before = start;
            while before > 0 && bytes[before - 1].is_ascii_whitespace() {
                before -= 1;
            }
            if before == 0 || after >= bytes.len() {
                continue;
            }
            match (bytes[before - 1], bytes[after]) {
                // `value["field"]`
                (b'[', b']') => count += 1,
                // `value.get("field")` / `value.get_mut("field")`
                (b'(', b')') => {
                    let mut ident_end = before - 1;
                    while ident_end > 0 && bytes[ident_end - 1].is_ascii_whitespace() {
                        ident_end -= 1;
                    }
                    let mut ident_start = ident_end;
                    while ident_start > 0
                        && (bytes[ident_start - 1].is_ascii_alphanumeric()
                            || bytes[ident_start - 1] == b'_')
                    {
                        ident_start -= 1;
                    }
                    if matches!(&text[ident_start..ident_end], "get" | "get_mut") {
                        count += 1;
                    }
                }
                _ => {}
            }
        }
        count
    }

    /// How many times `<ty>` is followed by optional whitespace and `{`, not as
    /// part of a longer identifier.
    fn count_braces(text: &str, ty: &str) -> usize {
        let bytes = text.as_bytes();
        let mut count = 0usize;
        for start in find_all(text, ty) {
            let end = start + ty.len();
            if end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                continue;
            }
            if start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_') {
                continue;
            }
            let mut after = end;
            while after < bytes.len() && bytes[after].is_ascii_whitespace() {
                after += 1;
            }
            if after < bytes.len() && bytes[after] == b'{' {
                count += 1;
            }
        }
        count
    }

    /// The mechanical definition of a read site for an ENUM VARIANT: the path
    /// `Type::Variant` appearing in code — a pattern, a construction or a
    /// comparison. This is the shape the previous scan could not see, and it is
    /// how `Inst`, `Ty`, `Constant` and `ProofEvidence` are actually read here.
    fn mentions_path(text: &str, path: &str) -> bool {
        let bytes = text.as_bytes();
        for start in find_all(text, path) {
            let end = start + path.len();
            if end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                continue;
            }
            if start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_') {
                continue;
            }
            return true;
        }
        false
    }

    /// The mechanical definition of a read site: field-access syntax.
    fn reads_field(text: &str, field: &str) -> bool {
        let bytes = text.as_bytes();
        let mut from = 0usize;
        while let Some(found) = text[from..].find(field) {
            let start = from + found;
            let end = start + field.len();
            from = start + 1;
            // Preceded by `.` (allowing whitespace/newlines, which rustfmt
            // introduces in long chains) and not part of a longer identifier.
            let mut before = start;
            while before > 0 && bytes[before - 1].is_ascii_whitespace() {
                before -= 1;
            }
            if before == 0 || bytes[before - 1] != b'.' {
                continue;
            }
            // `..` is a range or struct-update, not a field access.
            if before >= 2 && bytes[before - 2] == b'.' {
                continue;
            }
            if end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                continue;
            }
            return true;
        }
        false
    }

    /// Blank out comments and string literals, so the scan measures CODE.
    ///
    /// Without this the census counts itself: a doc comment that WRITES
    /// `compiler_facts.obligation_sources[].assertion_id`, or an error message
    /// that quotes a field path, would register as a read site, and the table
    /// would have to list every file that merely talks about a field. Both were
    /// observed while this module was being written.
    ///
    /// Deliberately a small scanner rather than a regex: it tracks line and
    /// (nesting) block comments, `"` strings with escapes, `'` char literals,
    /// and `r"`/`r#".."#` raw strings. Anything it blanks is replaced by a
    /// space, so byte offsets and line structure survive.
    fn strip_comments_and_strings(text: &str) -> String {
        blank_out(text, true)
    }

    /// Blank out comments only — the string-key scan needs the literals.
    fn strip_comments(text: &str) -> String {
        blank_out(text, false)
    }

    fn blank_out(text: &str, blank_strings: bool) -> String {
        let bytes = text.as_bytes();
        let mut out = vec![b' '; bytes.len()];
        let mut i = 0usize;
        while i < bytes.len() {
            let byte = bytes[i];
            // Line comment.
            if byte == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            // Block comment, nesting as Rust's do.
            if byte == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                let mut depth = 1usize;
                i += 2;
                while i < bytes.len() && depth > 0 {
                    if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                        depth += 1;
                        i += 2;
                    } else if bytes[i] == b'*' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                continue;
            }
            // Raw string: `r` followed by any number of `#` then `"`.
            if byte == b'r' {
                let mut hashes = 0usize;
                let mut j = i + 1;
                while j < bytes.len() && bytes[j] == b'#' {
                    hashes += 1;
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'"' {
                    // Not a raw string if `r` is part of a longer identifier.
                    let preceded_by_ident =
                        i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
                    if !preceded_by_ident {
                        let literal_start = i;
                        i = j + 1;
                        loop {
                            if i >= bytes.len() {
                                break;
                            }
                            if bytes[i] == b'"' {
                                let closing = bytes[i + 1..]
                                    .iter()
                                    .take(hashes)
                                    .filter(|byte| **byte == b'#')
                                    .count();
                                if closing == hashes {
                                    i += 1 + hashes;
                                    break;
                                }
                            }
                            i += 1;
                        }
                        if !blank_strings {
                            let end = i.min(bytes.len());
                            out[literal_start..end].copy_from_slice(&bytes[literal_start..end]);
                        }
                        continue;
                    }
                }
            }
            // Ordinary string.
            if byte == b'"' {
                let literal_start = i;
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                if !blank_strings {
                    let end = i.min(bytes.len());
                    out[literal_start..end].copy_from_slice(&bytes[literal_start..end]);
                }
                continue;
            }
            // Char literal — distinguished from a lifetime by the closing quote.
            if byte == b'\'' {
                let mut j = i + 1;
                if j < bytes.len() && bytes[j] == b'\\' {
                    j += 2;
                } else {
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'\'' {
                    i = j + 1;
                    continue;
                }
            }
            out[i] = byte;
            i += 1;
        }
        String::from_utf8_lossy(&out).into_owned()
    }

    fn collect_rust_sources(
        root: &std::path::Path,
        dir: &std::path::Path,
        out: &mut BTreeMap<String, String>,
    ) {
        collect_rust_sources_with(root, dir, out, strip_comments_and_strings);
    }

    fn collect_rust_sources_with(
        root: &std::path::Path,
        dir: &std::path::Path,
        out: &mut BTreeMap<String, String>,
        blank: fn(&str) -> String,
    ) {
        let entries = std::fs::read_dir(dir).expect("the crate's `src` directory is readable");
        for entry in entries {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                collect_rust_sources_with(root, &path, out, blank);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                let key = path
                    .strip_prefix(root)
                    .expect("path is under the scan root")
                    .to_string_lossy()
                    .replace('\\', "/");
                let text = std::fs::read_to_string(&path).expect("source file is readable");
                out.insert(key, blank(&text));
            }
        }
    }
}
