// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! THE EXPORT SEAM: the assertion id trust-vc STAMPS onto what it publishes.
//!
//! An evidence row, and the proof artifact minted from it, name the assertion
//! a certificate proves by a number. That number is what the fleet's coverage
//! join keys on (`lib.rs` `trust_ir_assertion_ids` / `covered_` / `missing_`),
//! so a row that names the wrong assertion publishes a proof of something
//! trust-vc never proved. This module decides which number, if any, a row may
//! publish.
//!
//! # The renderings
//!
//! A bundle carries one obligation's assertion identity in up to five places:
//!
//! | # | rendering | type | where |
//! |---|-----------|------|-------|
//! | A | `compiler_facts.obligation_sources[].assertion_id` | `u32` | the compiler-fact side table |
//! | B | `module.proof_obligations[].source.assertion_id` | `String` | the obligation's own source identity |
//! | C | `formula.payload` → source record `native_assertion_id` | `u32` | inside a JSON payload document |
//! | D | `formula.payload` → source record `assertion_id` | `String` | ditto |
//! | E | `provenance.replay_context.atoms[]` → `assertion_id` | `u32` | the `Assertion` replay atom the citing TrustVc request carries for the obligation |
//!
//! # The rule
//!
//! A certificate states its formula as ONE SMT-LIB text — its obligation's
//! `formula`, which is what trust-ir's replay grounds and what coverage rule 5
//! (`crate::native_coverage`) reads — and its assertion id in its own field:
//! rendering E. That is the atom Trust's `trust-ir-bridge` writes in every
//! TrustVc request (`native_replay_context`): an `Assertion` atom citing the
//! obligation, stating the obligation's formula cloned, and carrying the
//! compiler-fact number A.
//!
//! One digest binds the id to the certificate. The request digest
//! (`NativeVerificationRequest::stable_digest`) covers the request's
//! certificate references — each quotes the evidence digest of a certificate
//! whose CleanCic lineage covers the obligation's formula — and every atom's
//! formula text, obligation and `assertion_id`. trust-ir recomputes it against
//! the TrustVc evidence bundle, and this crate republishes it as
//! `request_digest` on the evidence row and in the artifact fingerprint. The
//! request digest does NOT cover an atom's formula `bindings`, so the input gate
//! below compares whole formulas, bindings included, rather than trusting the
//! digest for that.
//!
//! **The input gate** ([`validate_request_assertion_atoms`]) refuses the whole
//! bundle when, in any TrustVc request, a replay atom that cites an obligation:
//!
//! * cites one the module does not carry, or one its request does not list;
//! * carries an `assertion_id` other than that obligation's A (trust-ir refuses
//!   this first; the check is repeated here so this crate does not depend on
//!   it);
//! * is an `Assertion` atom whose formula is not EXACTLY its obligation's
//!   formula, bindings included. trust-ir-build checks atom formulas only for a
//!   solver-result basis, never for the kernel-replay basis that admits a
//!   TrustVc certificate, so this check is the only one that sees it;
//! * is a second `Assertion` atom for the same obligation that disagrees with
//!   the first about the id.
//!
//! **The evidence row** ([`AssertionIdCorroboration`]) publishes A only when
//! the request that cites the certificate carries EXACTLY ONE `Assertion` atom
//! for the obligation, that atom's id equals A, and A is not AMBIGUOUS in the
//! bundle ([`AssertionIdIndex`]): no other obligation carries the same number,
//! in a compiler fact, in a payload, in a replay atom of any request, or
//! through a string (B or D) that a numbered obligation carries; no replay
//! atom states it inside, or beside, a formula that is not its obligation's
//! own; no other formula the module states (a function summary clause, a spec
//! invariant or temporal formula) renders it, or a string that carries it,
//! unless that formula is exactly an obligation's own; and no payload anywhere
//! in the bundle renders an assertion identity unreadably (an unreadable
//! rendering might carry any number, so it withdraws every license in the
//! bundle). Unreadable means any payload that is not its schema's one accepted
//! shape (below). Otherwise it publishes no id, which is
//! a fail-closed
//! [`TrustVcNativeArtifactRejection::MissingAssertionId`]. The atom's id is
//! also recorded on the row as `independent_assertion_id`, and the artifact is
//! stamped only when every rendering the row carries agrees
//! ([`TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch`],
//! [`TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree`]). An atom
//! in another request, an atom citing a sibling obligation, or no atom at all
//! licenses nothing.
//!
//! A caller that names an id itself
//! (`TrustVcNativeTrustIrCertificateEvidence::admit_proof_artifact`) goes
//! through the same rule: it gets an accepted artifact only for the one id the
//! row licenses. Any other id, or any id at all on a row that licenses none, is
//! refused.
//!
//! # The payload renderings (C and D) refuse and never license
//!
//! C and D live in ONE record that the producer writes in two shapes: nested
//! under `source` in a [`TRUST_TYPES_FORMULA_SCHEMA_V1`] predicate document,
//! and at top level when the payload IS the source record
//! ([`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`]). Both shapes are read, and a
//! payload that renders the identity differently from A or B, or renders it
//! unreadably beside an A, refuses the bundle. An unreadable payload on an
//! obligation with no A does not refuse the bundle, but it withdraws every id
//! the bundle would publish ([`AssertionIdIndex`]). Neither licenses an id: a
//! payload that renders an id is a JSON document, not an SMT-LIB text, so
//! trust-ir never replays its certificate: the id and the formula would each
//! need the one payload.
//!
//! # The one accepted payload shape per schema
//!
//! The reader is STRICT (round 17). Rounds 14 to 16 each found one more shape
//! that carried an id past a reader that looked for the record and skipped
//! what it did not recognise: a number spelled `"1"`, a repeated key, a
//! document wrapped in an array, a key one level off. So the reader no longer
//! looks for the record. Each schema accepts exactly ONE shape, and every
//! payload under that schema that is not that shape is UNREADABLE, which fails
//! closed: beside an A it refuses the bundle, anywhere else it withdraws every
//! id the bundle would publish. The shape is `trust-ir-bridge`'s own
//! (`lower.rs`, `source_json`, `into_formula`, `safety_into_formula`,
//! `fail_closed_source_formula*`).
//!
//! Under [`TRUST_TYPES_FORMULA_SCHEMA_V1`], a JSON object with these keys and
//! no others:
//!
//! ```text
//! {
//!   "formula": <the predicate; any JSON value with no identity key in any object inside it>,
//!   "source": {
//!     "source_id":           <string>,
//!     "assertion_id":        <string>,            rendering D
//!     "native_assertion_id": <u32>,               rendering C
//!     "span": { "file": <string or u32>, "line_start": <u32>, "col_start": <u32>,
//!               "line_end": <u32>, "col_end": <u32> }
//!   }
//! }
//! ```
//!
//! Under [`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`], the record itself is the
//! document, with the same four keys plus the producer's three fail-closed
//! markers, and no others:
//!
//! ```text
//! {
//!   "source_id": <string>, "assertion_id": <string>, "native_assertion_id": <u32>,
//!   "span": { ... as above ... },
//!   "predicate_parse_failed": <string>, "attempted_predicate": <string>,
//!   "safety_formula_not_reconstructed": <string>
//! }
//! ```
//!
//! What the words mean:
//!
//! * **Every key is optional, and none may be added.** An absent key renders
//!   nothing: `{"formula": …}` with no `source` renders no identity, and a
//!   record without `native_assertion_id` renders no C. A key the shape does
//!   not have, at any level it defines (the predicate document's top, the
//!   record, its `span`), is unreadable whatever it holds, so a near miss
//!   (`nativeAssertionId`, `native_assertion_id ` with a trailing space), a
//!   `source` wrapper under the top-level schema, a marker inside a predicate
//!   document's record, or a note beside the predicate cannot carry an id this
//!   reader skips.
//! * **`<u32>` is an unsigned integer literal no larger than `u32::MAX`.**
//!   `"1"`, `1.0`, `1e0`, `-0`, `4294967297`, `null`, `[1]` and `{"0":1}` are
//!   not. Every other type is exact too: a string is a JSON string, an object a
//!   JSON object.
//! * **The document is an object.** An array, a string, a number, a boolean or
//!   null is unreadable under both schemas, even when it wraps the record.
//! * **No object repeats a key**, anywhere in the document, the predicate
//!   included. Keys are compared after escapes are decoded, so
//!   `native\u005fassertion_id` is `native_assertion_id`.
//! * **The predicate is not read, but it is searched.** Its keys are trust-ir's
//!   `Formula` tags, which this crate does not define, so its shape is left to
//!   the formula decoder; an object anywhere inside it that states
//!   `native_assertion_id` or `assertion_id` is unreadable.
//! * **A string VALUE is not a key.** `"attempted_predicate":
//!   "native_assertion_id == 1"` renders nothing.
//!
//! [`PayloadSourceBlock`] names which rule a payload broke. A payload under any
//! other schema is not parsed and renders nothing
//! ([`PayloadSourceBlock::NotDecoded`]): `trust-ir-bridge` writes an assertion
//! identity only under these two schemas. That is the one boundary of the
//! strict reader; an identity written under a third schema is neither read nor
//! refused here.
//!
//! # What corroborates nothing
//!
//! B, and every property of the bundle-wide map B -> A. "B -> A is a function"
//! is invariant under any relabeling of the numbers: replace every A in the
//! bundle by `f(A)` for an injective `f` and it still holds, so it cannot say
//! which assertion a number names. With A alone, a row's renderings are two
//! copies of one field (`assertion_id` and `compiler_facts_binding`), which
//! always agree, and the artifact-level cross-checks are vacuous. Moving
//! `compiler_facts.obligation_sources[1].assertion_id` 1 -> 0 in the
//! `discharge_scalar_branch` fixture then stamps trust-vc's proof of `clamp`'s
//! postcondition with the id of its precondition, which trust-vc only assumes.
//! The atom is what makes that edit a refusal: it carries its own copy of A,
//! under the request digest, beside the formula it asserts.
//!
//! # What this module deliberately does NOT do
//!
//! The real producer derives every number from one string. Measured in Trust's
//! `trust-ir-bridge`:
//!
//! ```text
//! lower.rs   native_assertion_id = trust_types::stable_u32_id(assertion_id.as_bytes())
//! native_request.rs
//!            assertion_id: Some(NativeAssertionId::new(
//!                trust_types::stable_u32_id(source.assertion_id.as_bytes())))
//! model.rs   stable_u32_id(b) = u32::from_be_bytes(sha256(b)[..4]), 0 mapped to 1
//! ```
//!
//! So for a Trust-rustc bundle `A == stable_u32_id(B)`, and this crate could
//! recompute it. It does not, on purpose: `stable_u32_id` is a property of ONE
//! producer, not of the trust-ir wire format. trust-ir's own conformance corpus
//! (`native_request_trust_bundle.json`, copied verbatim from upstream) numbers
//! its assertions 0/1/2 against strings `rust-assertion:0/1/2`, and so do this
//! crate's discharge fixtures; enforcing the derivation would refuse every
//! bundle upstream considers well-formed. A producer-scoped lane (one that knows
//! it is consuming trustc output) could turn it on as a strictly stronger check.
//!
//! # The residual: assertion numbering is producer-trusted
//!
//! Every check here compares renderings inside one bundle. None of them shows
//! that the number is the COMPILER's. Two shapes of one relabeling are
//! admitted:
//!
//! * **A move.** Move A and the atom's id together to a number no other
//!   obligation carries and reseal the request, and the certificate is admitted
//!   under the moved number while B still names the original string. The
//!   integration test
//!   `the_residual_a_fact_and_atom_moved_together_are_admitted_under_the_moved_number`
//!   pins this, so closing it flips that test. So does the move of a number
//!   taken from an UNREQUESTED obligation (trust-ir lets its fact lose the
//!   number) under a fresh string, pinned in
//!   `a_number_taken_from_an_unrequested_obligation_publishes_no_id`; taken
//!   with the victim's string, it is refused (the string still names it).
//! * **A permutation.** Swap the numbers of two obligations (with or without
//!   their strings), moving every rendering of each consistently, and reseal.
//!   After the swap every number is still carried by exactly one obligation, so
//!   nothing is ambiguous: obligation 0 is admitted under obligation 1's old
//!   number, and with two certified obligations each certificate is admitted
//!   under the other's old number. The integration test
//!   `the_residual_a_permutation_of_assertion_numbers_is_admitted_under_the_swapped_numbers`
//!   pins this.
//!
//! Both are a consistent relabeling (a move is a permutation with an unused
//! number), and the argument below covers both.
//!
//! **No anchor in the bundle can refuse it.** Each candidate, read at the
//! trust-ir pin:
//!
//! * The MIR assert site. `ProofObligation::site` is an IR coordinate
//!   (function, block, instruction index) and carries no number, and a
//!   def-site obligation has none. The module's IR carries no numeric
//!   assertion id anywhere: `NativeAssertionId` occurs only in the compiler-fact
//!   side table (A) and in replay atoms (E), the two fields the relabel moves.
//! * The source span. The obligation's `source.range` and the compiler fact's
//!   `span` name a location, and trust-ir already refuses an atom whose span
//!   differs from the fact's. No rule relates a location to a number.
//! * The request's obligation list. It lists `ProofId`s, not assertion
//!   numbers, and the relabel leaves it alone.
//! * The public obligation id (`vc:{def_path}:{kind}:{index}`) counts
//!   obligations, not assertions, and B is a string no wire rule derives the
//!   number from.
//!
//! The one derivation that does exist, `A == stable_u32_id(B)`, belongs to one
//! producer (above), and it would bind the number only to B, another field the
//! same producer writes and an editor can reseal.
//!
//! **Why that is the boundary.** This crate sees only the bundle, and whoever
//! wrote the bundle chose the numbers. Apply any injective relabeling of the
//! numbers consistently, in every fact and every atom that states them (a move
//! to an unused number, or a swap of two numbers): every check that does not
//! mention particular values, or a derivation the wire format fixes, still
//! passes. trust-ir fixes no such derivation. So no check here can tell the
//! compiler's numbering from a consistent relabeling. The numbering is trusted
//! to the producer, as much as its choice of which obligations to emit.
//!
//! **What an admitted id means.** Within THIS bundle, the number names exactly
//! one obligation: no other obligation carries it in any rendering or shares a
//! string with an obligation that does, no replay atom or other formula the
//! module states renders it inside another formula or states it beside one,
//! and every payload that could render it had its schema's one accepted shape
//! ([`AssertionIdIndex`]).
//! The certificate proves that
//! obligation's formula, the one SMT-LIB text trust-ir replays. The citing
//! request's digest binds the number to that formula.
//!
//! **What a consumer must NOT infer from it:**
//!
//! * that the number is the compiler's own numbering of that assertion, or that
//!   it equals `stable_u32_id` of anything;
//! * that it names the same assertion as the same number in another bundle,
//!   crate or build. Join an admitted id only against numbers read from the
//!   same bundle (the same `trust_ir_module_digest`). A coverage join against a
//!   list of compiler-emitted ids is sound only when that list and the bundle
//!   come from one producer run the consumer trusts;
//! * that admission vouches for the label. It vouches that the formula is
//!   proved. Which source assertion the number refers to is the producer's
//!   claim.
//!
//! What still publishes no id: a TrustVc request with no `Assertion` atom for
//! the obligation. trust-ir's conformance corpus is one such producer; its
//! TrustVc request carries no replay context.
//!
//! [`TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch`]: crate::native_artifact::TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch
//! [`TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree`]: crate::native_artifact::TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree
//! [`TrustVcNativeArtifactRejection::MissingAssertionId`]: crate::native_artifact::TrustVcNativeArtifactRejection::MissingAssertionId

use crate::TrustEngineError;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use trust_ir::request::{
    NativeObligationCause, NativeReplayAtom, NativeReplayAtomKind, NativeReplayContext,
    NativeVerificationRequest,
};
use trust_ir::{
    Module, NativeCompilerFacts, NativeObligationSource, ObligationKind, ProofFormula, ProofId,
    ProofObligation,
};

/// The payload schema whose NESTED `source` block carries renderings C and D.
///
/// `native_discharge::formula::ACCEPTED_FORMULA_SCHEMAS` is built from this
/// const so the decoder and this seam cannot drift onto different schema names.
pub(crate) const TRUST_TYPES_FORMULA_SCHEMA_V1: &str = "trust-types.Formula@1";

/// THE PRODUCER'S OTHER PAYLOAD SHAPE.
///
/// Trust's `trust-ir-bridge` emits [`TRUST_TYPES_FORMULA_SCHEMA_V1`] ONLY for an
/// obligation whose predicate it could render machine-readably: a parsed
/// contract predicate, or a reconstructed safety predicate. EVERY OTHER
/// obligation — a non-contract MIR assert with no reconstructed predicate, a
/// contract whose predicate did not parse, a safety class it declined to
/// reconstruct, the whole-function panic-freedom aggregate — goes out under
/// THIS schema, and its payload IS the source record: `source_id`,
/// `assertion_id`, `native_assertion_id` and `span` at TOP LEVEL, with no
/// `source` wrapper (`trust-ir-bridge` `lower.rs`, `source_json`).
///
/// Both shapes are read, and both only to REFUSE a payload that disagrees with
/// A or B (see the module docs): neither licenses an id.
///
/// This schema is deliberately NOT added to
/// `native_discharge::formula::ACCEPTED_FORMULA_SCHEMAS`: its payload carries no
/// predicate, so the discharge lane has nothing to decode from it. It renders an
/// IDENTITY, not a formula.
pub(crate) const TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1: &str = "trust.trust_ir.obligation-source.v1";

/// Every rendering of one obligation's assertion identity the bundle carries.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AssertionIdRenderings {
    /// A — `compiler_facts.obligation_sources[].assertion_id`.
    pub(crate) compiler_fact: Option<u32>,
    /// B — `module.proof_obligations[].source.assertion_id`.
    pub(crate) obligation_source: Option<String>,
    /// C — `formula.payload` -> `source.native_assertion_id`.
    pub(crate) payload_native: Option<u32>,
    /// D — `formula.payload` -> `source.assertion_id`.
    pub(crate) payload_source: Option<String>,
    /// E — the `assertion_id` of every `Assertion` replay atom that the CITING
    /// TrustVc request carries for this obligation, in atom order; `None` for
    /// an atom that states no id. `None` when the renderings were read without
    /// a request ([`Self::of`]), empty when the request carries no such atom.
    pub(crate) request_atoms: Option<Vec<Option<u32>>>,
    /// WHAT THE PAYLOAD'S `source` BLOCK ACTUALLY WAS, so that an absent block
    /// and a block that is not an object are stated facts, named in
    /// [`Self::describe`], rather than a silent "C and D are absent".
    pub(crate) payload_source_block: PayloadSourceBlock,
    /// The payload named a schema that carries C/D and is not the one shape
    /// that schema accepts (module docs, "The one accepted payload shape per
    /// schema"): it did not parse, repeated a key, was not an object where its
    /// schema needs one, carried a `source` that is not an object, stated an
    /// identity key outside its source record, carried a key its shape does not
    /// have, or a value of the wrong type. NOT the same as "absent": a
    /// rendering that is present and unreadable fails closed rather than being
    /// treated as missing.
    pub(crate) payload_unreadable: Option<String>,
}

/// WHAT THE DECODED PAYLOAD'S `source` BLOCK WAS — the state that used to be
/// silent.
///
/// A payload under [`TRUST_TYPES_FORMULA_SCHEMA_V1`] renders the assertion
/// identity inside a `source` object, and one under
/// [`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`] at top level, each in the one shape
/// the module docs write down. Every outcome is distinguishable, and only
/// [`Self::NotDecoded`], [`Self::Absent`], [`Self::Object`] and
/// [`Self::TopLevelObject`] are readable; every other state is a payload that
/// is not that shape:
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) enum PayloadSourceBlock {
    /// The obligation carries no formula, or one under a schema this seam does
    /// not decode. Nothing is claimed about its bytes.
    #[default]
    NotDecoded,
    /// A payload under the decoded schema that is not JSON at all. Fails closed
    /// through [`AssertionIdRenderings::payload_unreadable`].
    NotJson,
    /// A payload under the decoded schema that is JSON, but in which some
    /// object states one key twice (round 15). RFC 8259 §4 leaves which value
    /// a reader takes unspecified: `serde_json` keeps the LAST, other readers
    /// keep the first or refuse. So the document has no single reading, and it
    /// fails closed through [`AssertionIdRenderings::payload_unreadable`]
    /// exactly as [`Self::NotJson`] does. The check covers every object in the
    /// document, not only the source record, since a repeated `source` key at
    /// top level hides a whole record.
    RepeatedKey,
    /// A payload under [`TRUST_TYPES_FORMULA_SCHEMA_V1`] whose document is JSON
    /// but not an object: an array, a string, a number, a boolean or null
    /// (round 16). Such a document cannot say whether it carries a `source`
    /// record — `[{"source":{"native_assertion_id":1}}]` wraps one — so it is
    /// not [`Self::Absent`]; it fails closed through
    /// [`AssertionIdRenderings::payload_unreadable`], as
    /// [`Self::TopLevelNotAnObject`] does under the other schema.
    DocumentNotAnObject,
    /// A payload that states an identity key (`native_assertion_id` or
    /// `assertion_id`) in some object other than the record its schema reads
    /// (round 16): at the top of a predicate document, inside its `formula`,
    /// inside a `source` record's own nested objects, or in a `source` wrapper
    /// under the top-level schema. The producer writes the record in one place
    /// per schema, so a key elsewhere is a rendering this seam would otherwise
    /// skip. Unreadable, through [`AssertionIdRenderings::payload_unreadable`].
    StrayIdentityKey,
    /// A payload that is an object in the right place but not the one shape
    /// its schema accepts (round 17, the strict reader): a key that shape does
    /// not have at a level it defines (the predicate document's top, the source
    /// record, its `span`), or a value of the wrong type (`native_assertion_id`
    /// not a `u32`, `assertion_id` or `source_id` not a string, a `span` field
    /// of the wrong type, a marker that is not a string). Unreadable, through
    /// [`AssertionIdRenderings::payload_unreadable`].
    NotCanonical,
    /// A predicate document that is exactly `{"formula": …}`: an object with
    /// NO `source` key and no identity key anywhere. It renders no assertion
    /// identity, so the row publishes none — the decoder does not require the
    /// block (it requires `formula`), so this is not a bundle refusal, and
    /// saying so is the point of this variant.
    Absent,
    /// A `source` key that is not a JSON object. Present and unreadable, so it
    /// fails closed as a refusal rather than as an absence.
    NotAnObject,
    /// A readable `source` object. C and D are whatever it carries.
    Object,
    /// A payload under [`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`] whose document
    /// is not a JSON object at all. The document IS the source record under that
    /// schema, so this is the same present-and-unreadable state as
    /// [`Self::NotAnObject`], one nesting level up.
    TopLevelNotAnObject,
    /// A payload under [`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`]: the document
    /// itself is the source record, so C and D are read at top level. There is
    /// no wrapper that could be absent.
    TopLevelObject,
}

impl PayloadSourceBlock {
    /// How a refusal or a report should name this state.
    pub(crate) const fn label(&self) -> &'static str {
        match self {
            Self::NotDecoded => "no payload under a schema this seam decodes",
            Self::NotJson => "payload is not JSON",
            Self::RepeatedKey => "payload repeats a key inside one JSON object",
            Self::DocumentNotAnObject => "predicate payload document is not an object",
            Self::StrayIdentityKey => "payload states an identity key outside its source record",
            Self::NotCanonical => "payload is not the one shape its schema accepts",
            Self::Absent => "payload carries no `source` block",
            Self::NotAnObject => "payload `source` is not an object",
            Self::Object => "payload `source` object",
            Self::TopLevelNotAnObject => "payload document is not an object",
            Self::TopLevelObject => "payload document is itself the source record",
        }
    }
}

impl AssertionIdRenderings {
    /// Read every rendering for one obligation, with rendering E read from the
    /// replay context of the TrustVc request that cites its certificate.
    pub(crate) fn cited_by(
        obligation: &ProofObligation,
        source: Option<&NativeObligationSource>,
        request_context: &NativeReplayContext,
    ) -> Self {
        Self {
            request_atoms: Some(
                assertion_atoms_for(request_context, obligation.id)
                    .map(|atom| atom.assertion_id.map(|assertion_id| assertion_id.index()))
                    .collect(),
            ),
            ..Self::of(obligation, source)
        }
    }

    /// Read renderings A to D for one obligation. Rendering E belongs to a
    /// request, not to the module; see [`Self::cited_by`].
    pub(crate) fn of(
        obligation: &ProofObligation,
        source: Option<&NativeObligationSource>,
    ) -> Self {
        let payload = obligation
            .formula
            .as_ref()
            .map(Self::of_payload)
            .unwrap_or_default();
        Self {
            compiler_fact: source
                .and_then(|source| source.assertion_id.map(|assertion_id| assertion_id.index())),
            obligation_source: obligation
                .source
                .as_ref()
                .map(|source| source.assertion_id.clone()),
            ..payload
        }
    }

    /// Read renderings C and D, and the state of the payload's source record,
    /// from one formula. Every other field is left at its default.
    ///
    /// Used for an obligation's own formula ([`Self::of`]), and for the formula
    /// a replay atom states and every other formula the module states
    /// ([`AssertionIdIndex::of`]).
    ///
    /// THE READER IS STRICT (round 17): each schema has ONE accepted shape
    /// (the module docs, "The one accepted payload shape per schema"), and
    /// [`read_payload_identity`] reads C and D from that shape or from nothing.
    /// Every other shape is unreadable.
    fn of_payload(formula: &ProofFormula) -> Self {
        let mut renderings = Self::default();
        let shape = match formula.schema.as_str() {
            TRUST_TYPES_FORMULA_SCHEMA_V1 => PayloadShape::PredicateDocument,
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1 => PayloadShape::SourceRecord,
            // A schema this seam does not know renders nothing: its bytes are
            // not parsed and nothing is inferred from them.
            _ => return renderings,
        };
        match read_payload_identity(formula, shape) {
            Err(Unreadable { block, reason }) => {
                renderings.payload_source_block = block;
                renderings.payload_unreadable = Some(reason);
            }
            Ok(None) => renderings.payload_source_block = PayloadSourceBlock::Absent,
            Ok(Some(identity)) => {
                renderings.payload_source_block = match shape {
                    PayloadShape::PredicateDocument => PayloadSourceBlock::Object,
                    PayloadShape::SourceRecord => PayloadSourceBlock::TopLevelObject,
                };
                renderings.payload_native = identity.native_assertion_id;
                renderings.payload_source = identity.assertion_id;
            }
        }
        renderings
    }

    /// Name every rendering, present and absent, for a refusal message.
    ///
    /// A refusal that named only the two values that differ would leave a reader
    /// unable to tell WHICH rendering is the edited one.
    pub(crate) fn describe(&self) -> String {
        let rendering = |value: Option<String>| value.unwrap_or_else(|| "absent".to_string());
        let request_atoms = match self.request_atoms.as_deref() {
            None => "not read (no citing request)".to_string(),
            Some([]) => "no atom".to_string(),
            Some(atoms) => atoms
                .iter()
                .map(|atom| rendering(atom.map(|value| value.to_string())))
                .collect::<Vec<_>>()
                .join(", "),
        };
        format!(
            "A `compiler_facts.obligation_sources[].assertion_id` = {}; \
             B `proof_obligations[].source.assertion_id` = {}; \
             C payload source record `native_assertion_id` = {}; \
             D payload source record `assertion_id` = {}; \
             E citing request's `Assertion` replay atom `assertion_id` = {request_atoms}; \
             payload source record = {}{}",
            rendering(self.compiler_fact.map(|value| value.to_string())),
            rendering(
                self.obligation_source
                    .as_ref()
                    .map(|value| format!("{value:?}"))
            ),
            rendering(self.payload_native.map(|value| value.to_string())),
            rendering(
                self.payload_source
                    .as_ref()
                    .map(|value| format!("{value:?}"))
            ),
            self.payload_source_block.label(),
            self.payload_unreadable
                .as_ref()
                .map(|reason| format!("; payload UNREADABLE: {reason}"))
                .unwrap_or_default(),
        )
    }
}

/// The keys a payload source record renders an assertion identity under: C and
/// D.
const IDENTITY_KEYS: [&str; 2] = ["native_assertion_id", "assertion_id"];

/// What kind of JSON value `value` is, for a refusal message.
fn json_kind(value: &serde_json::Value) -> &'static str {
    match value {
        serde_json::Value::Null => "null",
        serde_json::Value::Bool(_) => "a boolean",
        serde_json::Value::Number(_) => "a number",
        serde_json::Value::String(_) => "a string",
        serde_json::Value::Array(_) => "an array",
        serde_json::Value::Object(_) => "an object",
    }
}

/// The path of the first identity key (C or D) that `value` states in any
/// object other than `record`, the one object the payload's schema reads them
/// from. `None` when every identity key in the document is the record's own.
///
/// `record` is compared by address, so an object elsewhere in the document with
/// the same contents is still a stray one. Objects nested inside the record
/// (its `span`) are not the record either. Keys are compared after escapes are
/// decoded, as the rest of the read does.
fn stray_identity_key(
    value: &serde_json::Value,
    record: Option<&serde_json::Value>,
    path: &mut Vec<String>,
) -> Option<String> {
    let found = |path: &[String], key: &str| {
        let mut found = String::from("$");
        for segment in path {
            found.push_str(segment);
        }
        found.push('.');
        found.push_str(key);
        found
    };
    match value {
        serde_json::Value::Object(object) => {
            let is_record = record.is_some_and(|record| std::ptr::eq(record, value));
            if !is_record {
                if let Some(key) = IDENTITY_KEYS.iter().find(|key| object.contains_key(**key)) {
                    return Some(found(path, key));
                }
            }
            for (key, child) in object {
                path.push(format!(".{key}"));
                let stray = stray_identity_key(child, record, path);
                path.pop();
                if stray.is_some() {
                    return stray;
                }
            }
            None
        }
        serde_json::Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                path.push(format!("[{index}]"));
                let stray = stray_identity_key(child, record, path);
                path.pop();
                if stray.is_some() {
                    return stray;
                }
            }
            None
        }
        _ => None,
    }
}

/// Which of the two accepted shapes a payload's schema names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PayloadShape {
    /// [`TRUST_TYPES_FORMULA_SCHEMA_V1`]: a predicate document, with the source
    /// record under `source`.
    PredicateDocument,
    /// [`TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1`]: the document IS the source
    /// record.
    SourceRecord,
}

/// The keys a predicate document may carry. Nothing else, at its top level.
const PREDICATE_DOCUMENT_KEYS: [&str; 2] = ["formula", "source"];

/// The keys a source record may carry under either schema, with their types:
/// `source_id` a string, `assertion_id` (D) a string, `native_assertion_id` (C)
/// a `u32`, `span` a span object ([`SPAN_KEYS`]).
const SOURCE_RECORD_KEYS: [&str; 4] = ["source_id", "assertion_id", "native_assertion_id", "span"];

/// The fail-closed markers `trust-ir-bridge` adds to a TOP-LEVEL source record
/// (`fail_closed_source_formula`, `fail_closed_source_formula_with_predicate`,
/// `safety_into_formula`), each a string. Not accepted inside a predicate
/// document's `source`: the producer never writes them there.
const SOURCE_RECORD_MARKER_KEYS: [&str; 3] = [
    "predicate_parse_failed",
    "attempted_predicate",
    "safety_formula_not_reconstructed",
];

/// The keys a record's `span` may carry: `file` a string or a `u32`, the rest
/// `u32`s. `file` is a string in `trust-ir-bridge`'s `source_json` and a `u32`
/// file index in this crate's checked-in discharge fixtures; a span renders no
/// identity, so both are read, and nothing else is.
const SPAN_KEYS: [&str; 5] = ["file", "line_start", "col_start", "line_end", "col_end"];

/// A payload the strict reader refuses: the state it reports, and why.
struct Unreadable {
    block: PayloadSourceBlock,
    reason: String,
}

/// What the one accepted shape renders: C and D, each `None` when its key is
/// absent.
#[derive(Debug, Default)]
struct PayloadIdentity {
    native_assertion_id: Option<u32>,
    assertion_id: Option<String>,
}

/// A JSON value as a `u32`, when it is written as one: an unsigned integer
/// literal no larger than `u32::MAX`. `"1"`, `1.0`, `1e0`, `-0`, `4294967297`,
/// `null`, `[1]` and `{"0":1}` are not.
fn exact_u32(value: &serde_json::Value) -> Option<u32> {
    value.as_u64().and_then(|value| u32::try_from(value).ok())
}

/// THE STRICT IDENTITY READER: C and D from the one shape `shape` accepts.
///
/// `Ok(None)` is a predicate document with no `source` key: it renders no
/// identity. `Ok(Some(_))` is a source record in its one place with only its
/// own keys, each of its own type. Everything else is [`Unreadable`], in this
/// order: not JSON; a key repeated in some object; a document that is not an
/// object; a `source` that is not an object; an identity key in any object but
/// the record (inside the predicate too); any key the shape does not have, at
/// any level it defines; any value of the wrong type. The shape is written
/// down in the module docs, "The one accepted payload shape per schema".
fn read_payload_identity(
    formula: &ProofFormula,
    shape: PayloadShape,
) -> Result<Option<PayloadIdentity>, Unreadable> {
    let schema = formula.schema.as_str();
    let unreadable = |block: PayloadSourceBlock, reason: String| Unreadable { block, reason };
    let not_canonical = |reason: String| {
        unreadable(
            PayloadSourceBlock::NotCanonical,
            format!(
                "payload under schema `{schema}` is not the one shape that schema accepts: \
                 {reason}"
            ),
        )
    };
    let document: serde_json::Value = serde_json::from_str(&formula.payload).map_err(|error| {
        unreadable(
            PayloadSourceBlock::NotJson,
            format!("payload under schema `{schema}` is not JSON: {error}"),
        )
    })?;
    // ROUND 15. `serde_json::Value` keeps the LAST value of a repeated key and
    // says nothing, so `{"native_assertion_id":"1","native_assertion_id":7}`
    // read as a readable 7 while the unreadable "1" sat in the bytes. A
    // document with a repeated key has no single reading, whatever the key and
    // wherever the object.
    serde_json::from_str::<NoRepeatedKey>(&formula.payload).map_err(|error| {
        unreadable(
            PayloadSourceBlock::RepeatedKey,
            format!(
                "payload under schema `{schema}` repeats a key inside one JSON object \
                 ({error}); RFC 8259 leaves which value a reader takes unspecified, so no \
                 single rendering can be read from it"
            ),
        )
    })?;
    // ROUND 16. Both shapes are objects. `Value::get` answers `None` for an
    // array, a string, a number, a bool and null alike, so a predicate document
    // `[{"formula":…,"source":{"native_assertion_id":1}}]` used to read as one
    // with no source record.
    let Some(document_object) = document.as_object() else {
        return Err(match shape {
            PayloadShape::PredicateDocument => unreadable(
                PayloadSourceBlock::DocumentNotAnObject,
                format!(
                    "payload under schema `{schema}` is {}, not a JSON object, so whether it \
                     carries a source record cannot be read",
                    json_kind(&document)
                ),
            ),
            PayloadShape::SourceRecord => unreadable(
                PayloadSourceBlock::TopLevelNotAnObject,
                format!(
                    "the payload's source record is {document}, which is not an object, so \
                     the payload's renderings of the assertion identity cannot be read"
                ),
            ),
        });
    };
    // The one place the record may be.
    let record = match shape {
        PayloadShape::PredicateDocument => document_object.get("source"),
        PayloadShape::SourceRecord => Some(&document),
    };
    let record_object = match record {
        None => None,
        Some(record) => match record.as_object() {
            Some(record_object) => Some(record_object),
            None => {
                return Err(unreadable(
                    PayloadSourceBlock::NotAnObject,
                    format!(
                        "the payload's source record is {record}, which is not an object, so \
                         the payload's renderings of the assertion identity cannot be read"
                    ),
                ));
            }
        },
    };
    // ROUND 16. An identity key in any object but the record: at the top of a
    // predicate document, inside the predicate, inside the record's `span`, or
    // in a `source` wrapper under the top-level schema. The walk also covers
    // the predicate, whose keys this crate does not define (they are trust-ir's
    // `Formula` tags), so an identity key there is found by name.
    let mut path = Vec::new();
    if let Some(stray) = stray_identity_key(&document, record, &mut path) {
        return Err(unreadable(
            PayloadSourceBlock::StrayIdentityKey,
            format!(
                "payload under schema `{schema}` states an assertion identity key at \
                 `{stray}`, outside the source record that schema carries, so which \
                 rendering it means cannot be read"
            ),
        ));
    }
    // ROUND 17, THE STRICT SHAPE. Every level this crate defines has a closed
    // key set, and every value its type. A key the shape does not have (an
    // `assertion` beside the record, a `nativeAssertionId` inside it, a `source`
    // wrapper under the top-level schema) is a place another reader might find
    // an identity this one skips, so it is unreadable whatever it holds.
    if shape == PayloadShape::PredicateDocument {
        if let Some(key) = document_object
            .keys()
            .find(|key| !PREDICATE_DOCUMENT_KEYS.contains(&key.as_str()))
        {
            return Err(not_canonical(format!(
                "it carries the key `$.{key}`, and a predicate document carries `formula` \
                 and `source` only"
            )));
        }
    }
    let Some(record_object) = record_object else {
        return Ok(None);
    };
    let (record_path, markers): (&str, &[&str]) = match shape {
        PayloadShape::PredicateDocument => ("$.source", &[]),
        PayloadShape::SourceRecord => ("$", &SOURCE_RECORD_MARKER_KEYS),
    };
    // The closed key set first: a key the record does not have is refused
    // whatever it holds. Then each key the record may have, by name, with its
    // type. (Each read is a plain `get("<key>")`, so the string-key census in
    // `producer_fields.rs` counts it.)
    if let Some(other) = record_object
        .keys()
        .find(|key| !SOURCE_RECORD_KEYS.contains(&key.as_str()) && !markers.contains(&key.as_str()))
    {
        let accepted = SOURCE_RECORD_KEYS
            .iter()
            .chain(markers)
            .map(|key| format!("`{key}`"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(not_canonical(format!(
            "the source record carries the key `{record_path}.{other}`, and it carries \
             {accepted} only"
        )));
    }
    let mut identity = PayloadIdentity::default();
    if let Some(value) = record_object.get("native_assertion_id") {
        let Some(native) = exact_u32(value) else {
            return Err(not_canonical(format!(
                "the source record renders `native_assertion_id` as {value}, which is not a \
                 u32"
            )));
        };
        identity.native_assertion_id = Some(native);
    }
    if let Some(value) = record_object.get("assertion_id") {
        let Some(assertion_id) = value.as_str() else {
            return Err(not_canonical(format!(
                "the source record renders `assertion_id` as {value}, which is not a string"
            )));
        };
        identity.assertion_id = Some(assertion_id.to_string());
    }
    // Read for its TYPE only; its value is never used.
    if let Some(value) = record_object.get("source_id") {
        if !value.is_string() {
            return Err(not_canonical(format!(
                "`{record_path}.source_id` is {value}, which is not a string"
            )));
        }
    }
    // Read for its SHAPE only; its values are never used.
    if let Some(span) = record_object.get("span") {
        if let Some(reason) = span_not_canonical(span, record_path) {
            return Err(not_canonical(reason));
        }
    }
    for marker in markers {
        if let Some(value) = record_object.get(*marker) {
            if !value.is_string() {
                return Err(not_canonical(format!(
                    "`{record_path}.{marker}` is {value}, which is not a string"
                )));
            }
        }
    }
    Ok(Some(identity))
}

/// Why a record's `span` is not the accepted span object ([`SPAN_KEYS`]), or
/// `None` when it is.
fn span_not_canonical(span: &serde_json::Value, record_path: &str) -> Option<String> {
    let Some(span) = span.as_object() else {
        return Some(format!(
            "`{record_path}.span` is {}, not an object",
            json_kind(span)
        ));
    };
    if let Some(other) = span.keys().find(|key| !SPAN_KEYS.contains(&key.as_str())) {
        return Some(format!(
            "the span carries the key `{record_path}.span.{other}`, and it carries {} only",
            SPAN_KEYS
                .iter()
                .map(|key| format!("`{key}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if let Some(file) = span.get("file") {
        if !file.is_string() && exact_u32(file).is_none() {
            return Some(format!(
                "`{record_path}.span.file` is {file}, which is not a string or a u32"
            ));
        }
    }
    for (key, value) in [
        ("line_start", span.get("line_start")),
        ("col_start", span.get("col_start")),
        ("line_end", span.get("line_end")),
        ("col_end", span.get("col_end")),
    ] {
        if let Some(value) = value.filter(|value| exact_u32(value).is_none()) {
            return Some(format!(
                "`{record_path}.span.{key}` is {value}, which is not a u32"
            ));
        }
    }
    None
}

/// A JSON document read ONLY to find an object that states one key twice.
///
/// Deserializing it walks every value in the document and fails on the first
/// object whose keys repeat. Keys are compared after escapes are decoded, so
/// `"native_assertion_id"` and `"native\u005fassertion_id"` are the same key,
/// as they are to the `serde_json::Value` read that follows. It keeps nothing:
/// success means only "no object in this document repeats a key".
struct NoRepeatedKey;

impl<'de> serde::Deserialize<'de> for NoRepeatedKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(NoRepeatedKeyVisitor)
    }
}

struct NoRepeatedKeyVisitor;

impl<'de> serde::de::Visitor<'de> for NoRepeatedKeyVisitor {
    type Value = NoRepeatedKey;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_bool<E>(self, _: bool) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_i64<E>(self, _: i64) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_u64<E>(self, _: u64) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_f64<E>(self, _: f64) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_str<E>(self, _: &str) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(NoRepeatedKey)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        serde::Deserialize::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        while seq.next_element::<NoRepeatedKey>()?.is_some() {}
        Ok(NoRepeatedKey)
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if keys.contains(&key) {
                return Err(serde::de::Error::custom(format_args!(
                    "the key {key:?} appears twice in one object"
                )));
            }
            map.next_value::<NoRepeatedKey>()?;
            keys.insert(key);
        }
        Ok(NoRepeatedKey)
    }
}

/// WHICH NUMERIC ASSERTION IDS THIS BUNDLE CANNOT USE AS IDENTITIES.
///
/// **The rule, in effect: a number carried by two or more obligations
/// publishes no id, for any of them.** The code compares carriers by
/// [`CarrierIdentity`] (formulas, public obligation ids, `source.assertion_id`
/// strings), but at the trust-ir pin two different obligations never compare
/// equal there: trust-ir refuses two compiler facts with one
/// `public_obligation_id` (`DuplicatePublicObligationSource`), and a row can be
/// licensed only through its compiler fact, so a licensable row's public id is
/// always present and never shared. So neither a shared formula nor a shared
/// string ever lets two obligations share a number. This also withdraws the id
/// from a LEGITIMATE assertion with several obligations, which trust-ir allows
/// (`NativeCompilerFacts::obligations_for_assertion`); that fails closed, and
/// is accepted as the price.
///
/// An ambiguous number names none of its carriers, and every row whose
/// compiler fact carries it publishes NO id (a fail-closed `MissingAssertionId`
/// on the artifact). The rest of the bundle is untouched.
///
/// "Carries" means every numeric rendering in the bundle, not only A: the
/// compiler fact (A), the payload's `native_assertion_id` (C), and the
/// `assertion_id` of a replay atom that cites the obligation, in ANY request
/// (E). trust-ir and the input gates already make C and E agree with A where
/// the obligation has a compiler fact, so these add carriers only where it has
/// none. A replay atom's FORMULA is read too, in every request: a formula that
/// is exactly its cited obligation's formula is that obligation's own
/// rendering (already counted), and any other formula that renders a number
/// makes that number ambiguous, because it gives the number to a formula no
/// obligation states.
///
/// **Every formula the module states is read the same way** (round 15). Round
/// 14 read obligation formulas and atom formulas only, so the same hole stayed
/// open one field over: a function summary's `ensures` clause rendering
/// obligation 0's number (readably, unreadably, or as bytes that are not JSON)
/// left obligation 0 admitted under 1, in both lanes, while the docs already
/// said an unreadable payload anywhere in the bundle withdraws every id. The
/// index now walks trust-ir's inventory of stated formulas
/// (`Module::stated_formulas_iter`: obligations, summary `requires` /
/// `ensures` / `decreases`, spec typed invariants, temporal formulas). A
/// formula exactly equal to an obligation's own is that obligation's
/// rendering; any other that renders a number makes it ambiguous, and any
/// that renders unreadably withdraws every license.
///
/// **An unreadable rendering withdraws EVERY license in the bundle** (round
/// 14). A payload under a schema this seam decodes that is not that schema's
/// one accepted shape (module docs; round 17) — not JSON, a key repeated
/// inside one JSON object (round 15), a predicate document that is not an
/// object or an identity key outside the record the schema reads (round 16), a
/// source record that is not an object, a key the shape does not have, a
/// `native_assertion_id` that is not a `u32` (`"1"`, `1.0`, `4294967297`), an
/// `assertion_id` that is not a string — might carry ANY number, so every
/// number is ambiguous. Counting only the readable ones was the fail-open this
/// module forbids elsewhere: an unrequested obligation with no compiler fact,
/// whose payload spelled obligation 0's number as `"1"`, was not counted, and
/// obligation 0 was admitted under 1 while the same number written as a `u32`
/// was refused. [`validate_assertion_id_renderings`] cannot refuse such a
/// payload itself (it refuses only beside an A, so that one unrequested row
/// does not kill the bundle, round 9), and trust-ir never sees the payload's
/// JSON. So the bundle is still consumed, and it publishes no id at all.
///
/// **Round 16 adds two carriers.** An atom's OWN id stated beside a formula
/// that is not its cited obligation's gives the number to that formula (the
/// producer writes an atom's id only beside its obligation's formula cloned),
/// whatever the atom's kind and request. And an obligation carries every
/// number its string (B, or D) carries anywhere in the bundle: B -> A is a
/// function, so an unnumbered obligation that shares a numbered one's string
/// still names that number, and a stray formula that renders the string (D)
/// gives the number to itself. Without this, deleting an unrequested victim's
/// number and giving its string and number to obligation 0 left one carrier.
/// This closes only the copy-the-string variant: the same move under a fresh
/// string is the documented move residual.
///
/// WHY NOT THE STRINGS ALONE (round 13). This index used to call a number
/// ambiguous only when two DIFFERENT `source.assertion_id` strings shared it.
/// That missed an edit that moves the string with the number. Copy obligation
/// 1's whole identity (string `rust-assertion:2`, compiler fact 2, atom id 2)
/// onto obligation 0 and reseal: the strings agree, B -> A is still a function,
/// the atom equals the fact, and obligation 0's proof of `(>= 5 0)` was
/// published as assertion 2 while obligation 1 still carried 2 for another
/// formula. Relabeling obligations 0 and 1 to one fresh identity
/// (`rust-assertion:9` / 9) passed the same way. Two obligations with
/// different formulas or different public ids are two assertions, whatever
/// string they share, and a number they share names neither.
///
/// A collision is not a bundle refusal. The real producer derives the number
/// as `stable_u32_id(b) = u32::from_be_bytes(sha256(b)[..4])` with 0 remapped to
/// 1 (see the module docs), a TRUNCATED 32-bit hash: ~10k source assertions
/// collide with probability ~1%, and the 0 -> 1 remap makes one collision pair
/// certain by definition. Refusing the bundle would accuse a producer of
/// disagreeing with itself when it is behaving exactly as documented. So a
/// collision is a LOST IDENTITY, not an error.
///
/// One `source.assertion_id` string carrying two different numbers stays a
/// refusal, in [`validate_assertion_id_renderings`]: that is a contradiction
/// under ANY derivation, not a property of one producer.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AssertionIdIndex {
    ambiguous: BTreeSet<u32>,
    /// The first unreadable rendering found, named. When set, EVERY number is
    /// ambiguous (see above).
    unreadable: Option<String>,
}

/// What two obligations sharing a number must agree on for the number to name
/// one assertion. An obligation the module does not carry is its own identity,
/// equal to no other.
#[derive(Debug, PartialEq, Eq)]
enum CarrierIdentity<'a> {
    Known {
        /// `compiler_facts.obligation_sources[].public_obligation_id`.
        public_obligation_id: Option<&'a str>,
        /// `module.proof_obligations[].source.public.obligation_id`.
        embedded_public_obligation_id: Option<&'a str>,
        /// The obligation's formula, bindings included.
        formula: Option<&'a ProofFormula>,
        /// B, `module.proof_obligations[].source.assertion_id`.
        assertion_string: Option<&'a str>,
    },
    Unknown(ProofId),
}

impl AssertionIdIndex {
    /// Index every numeric rendering of an assertion identity in the bundle:
    /// compiler facts, obligation payloads, every other formula the module
    /// states, and the replay atoms of every request.
    pub(crate) fn of(
        module: &Module,
        compiler_facts: &NativeCompilerFacts,
        requests: &[NativeVerificationRequest],
    ) -> Self {
        let obligations = module
            .proof_obligations
            .iter()
            .map(|obligation| (obligation.id, obligation))
            .collect::<BTreeMap<_, _>>();
        let identity = |obligation_id: ProofId| -> CarrierIdentity<'_> {
            let Some(obligation) = obligations.get(&obligation_id).copied() else {
                return CarrierIdentity::Unknown(obligation_id);
            };
            CarrierIdentity::Known {
                public_obligation_id: compiler_facts
                    .obligation_source(obligation_id)
                    .map(|source| source.public_obligation_id.as_str()),
                embedded_public_obligation_id: obligation
                    .source
                    .as_ref()
                    .and_then(|source| source.public.as_ref())
                    .map(|public| public.obligation_id.as_str()),
                formula: obligation.formula.as_ref(),
                assertion_string: obligation
                    .source
                    .as_ref()
                    .map(|source| source.assertion_id.as_str()),
            }
        };

        let mut carriers: BTreeMap<u32, Vec<ProofId>> = BTreeMap::new();
        fn carry(carriers: &mut BTreeMap<u32, Vec<ProofId>>, numeric: u32, obligation_id: ProofId) {
            let carried = carriers.entry(numeric).or_default();
            if !carried.contains(&obligation_id) {
                carried.push(obligation_id);
            }
        }
        // Numbers a rendering gives to a formula no obligation states as its
        // own: ambiguous whoever else carries them.
        let mut stray: BTreeSet<u32> = BTreeSet::new();
        // Strings (D) a rendering gives to a formula no obligation states as its
        // own: every number that string carries is ambiguous (round 16).
        let mut stray_strings: BTreeSet<String> = BTreeSet::new();
        // Every obligation's string identity: B, and the payload's D.
        let mut strings: Vec<(String, ProofId)> = Vec::new();
        // The first unreadable rendering. It withdraws every license.
        let mut unreadable: Option<String> = None;
        let mut withdraw = |reason: String| {
            unreadable.get_or_insert(reason);
        };
        // A: every compiler fact, including one for an obligation the module
        // does not carry.
        for source in &compiler_facts.obligation_sources {
            if let Some(assertion_id) = source.assertion_id {
                carry(&mut carriers, assertion_id.index(), source.obligation);
            }
        }
        // C: every payload that renders a number, and every payload that
        // renders one unreadably. B and D are collected for the string classes
        // below.
        for obligation in &module.proof_obligations {
            let renderings = AssertionIdRenderings::of(
                obligation,
                compiler_facts.obligation_source(obligation.id),
            );
            if let Some(reason) = renderings.payload_unreadable {
                withdraw(format!(
                    "obligation {}'s formula payload: {reason}",
                    obligation.id.index()
                ));
            }
            if let Some(payload_native) = renderings.payload_native {
                carry(&mut carriers, payload_native, obligation.id);
            }
            for string in [renderings.obligation_source, renderings.payload_source]
                .into_iter()
                .flatten()
            {
                strings.push((string, obligation.id));
            }
        }
        // EVERY OTHER FORMULA THE MODULE STATES (round 15): each function
        // summary's `requires`, `ensures` and `decreases` clause, each spec
        // machine's typed invariant and each temporal formula. The walk is
        // trust-ir's own inventory, `Module::stated_formulas_iter`, which trust-ir
        // keeps complete for its one-formula rule ("a new place that stores a
        // `ProofFormula` in a module belongs here"), so a carrier added upstream
        // is read here without a change in this crate. A formula exactly equal to
        // an obligation's own (bindings included) is that obligation's rendering
        // and was read above; a proved summary's clause is one of those, since
        // trust-ir-build requires it to equal its backing obligation's formula.
        // Any other formula that renders a number gives it to a formula no
        // obligation states, and one that renders unreadably might give any.
        let own_formulas = module
            .proof_obligations
            .iter()
            .filter_map(|obligation| obligation.formula.as_ref())
            .collect::<HashSet<_>>();
        for (site, formula) in module.stated_formulas_iter() {
            let payload = AssertionIdRenderings::of_payload(formula);
            if payload.payload_unreadable.is_none()
                && payload.payload_native.is_none()
                && payload.payload_source.is_none()
            {
                continue;
            }
            if own_formulas.contains(formula) {
                continue;
            }
            if let Some(reason) = payload.payload_unreadable {
                withdraw(format!("{site}'s formula payload: {reason}"));
            }
            if let Some(payload_native) = payload.payload_native {
                stray.insert(payload_native);
            }
            if let Some(payload_source) = payload.payload_source {
                stray_strings.insert(payload_source);
            }
        }
        // E: every replay atom, of every request and every kind, that cites an
        // obligation and states a number. And every atom's FORMULA: one that is
        // exactly its cited obligation's formula was read above; any other that
        // renders a number gives it to a formula no obligation states.
        for request in requests {
            for atom in &request.provenance().replay_context.atoms {
                if let (Some(obligation_id), Some(assertion_id)) =
                    (atom.obligation, atom.assertion_id)
                {
                    carry(&mut carriers, assertion_id.index(), obligation_id);
                }
                let cited_formula = atom
                    .obligation
                    .and_then(|obligation_id| obligations.get(&obligation_id))
                    .and_then(|obligation| obligation.formula.as_ref());
                if cited_formula == Some(&atom.formula) {
                    continue;
                }
                // ROUND 16: the atom's OWN id, stated beside a formula that is
                // not its cited obligation's. Round 14 read only the number the
                // atom's formula renders, so an atom in a TrustWp or TrustMc
                // request (whose atoms the TrustVc gate never reads), or an
                // `Assumption` atom in the citing TrustVc request (whose formula
                // that gate compares only for `Assertion` atoms), could cite
                // obligation 0 with its number 1 while asserting obligation 1's
                // formula, and 1 stayed licensed. The producer writes an atom's
                // id only beside its obligation's own formula cloned, so the
                // number now names two formulas and names neither. An atom that
                // cites no obligation, or one the module does not carry, gives
                // its id to no obligation's formula at all.
                if let Some(assertion_id) = atom.assertion_id {
                    stray.insert(assertion_id.index());
                }
                let payload = AssertionIdRenderings::of_payload(&atom.formula);
                if let Some(reason) = payload.payload_unreadable {
                    withdraw(format!(
                        "request {}'s {:?} replay atom #{}'s formula payload: {reason}",
                        request.id().index(),
                        atom.kind,
                        atom.id.index()
                    ));
                }
                if let Some(payload_native) = payload.payload_native {
                    stray.insert(payload_native);
                }
                if let Some(payload_source) = payload.payload_source {
                    stray_strings.insert(payload_source);
                }
            }
        }

        // ROUND 16, THE STRING CLASSES. An obligation carries every number its
        // string (B or D) carries anywhere in the bundle. Without this, an
        // UNNUMBERED obligation was no carrier at all: delete an unrequested
        // victim's number (obligation 7, `rust-assertion:7`, fact 7), give
        // obligation 0 the string and the number, and 7 had one carrier, so
        // obligation 0 was admitted under 7 while obligation 7 still named
        // `rust-assertion:7` for another formula. B -> A is a function (the
        // input gate refuses one string under two numbers), so the victim's
        // string still names 7, and 7 now has two carriers. A formula no
        // obligation states that renders a string (D) gives every number that
        // string carries to that formula, as a rendered number (C) does.
        //
        // This closes only the copy-the-string variant. Moving the thief to a
        // FRESH string with the victim's old number is the documented move
        // residual: no field left in the bundle ties that number to anything.
        let mut numbers_of: BTreeMap<ProofId, BTreeSet<u32>> = BTreeMap::new();
        for (numeric, carried) in &carriers {
            for obligation_id in carried {
                numbers_of
                    .entry(*obligation_id)
                    .or_default()
                    .insert(*numeric);
            }
        }
        let mut numbers_by_string: BTreeMap<&str, BTreeSet<u32>> = BTreeMap::new();
        for (string, obligation_id) in &strings {
            let numbers = numbers_by_string.entry(string.as_str()).or_default();
            if let Some(carried) = numbers_of.get(obligation_id) {
                numbers.extend(carried.iter().copied());
            }
        }
        for (string, obligation_id) in &strings {
            for numeric in &numbers_by_string[string.as_str()] {
                carry(&mut carriers, *numeric, *obligation_id);
            }
        }
        for string in &stray_strings {
            if let Some(numbers) = numbers_by_string.get(string.as_str()) {
                stray.extend(numbers.iter().copied());
            }
        }

        let mut ambiguous = carriers
            .into_iter()
            .filter(|(_, carried)| {
                carried
                    .iter()
                    .skip(1)
                    .any(|other| identity(*other) != identity(carried[0]))
            })
            .map(|(numeric, _)| numeric)
            .collect::<BTreeSet<_>>();
        ambiguous.extend(stray);
        Self {
            ambiguous,
            unreadable,
        }
    }

    /// Whether this number may not be published as an identity: more than one
    /// assertion identity in the bundle carries it, or some rendering in the
    /// bundle is unreadable and so might carry it.
    pub(crate) fn is_ambiguous(&self, numeric: u32) -> bool {
        self.unreadable.is_some() || self.ambiguous.contains(&numeric)
    }

    /// The unreadable rendering that withdrew every license, if one did.
    #[cfg(test)]
    fn unreadable(&self) -> Option<&str> {
        self.unreadable.as_deref()
    }
}

/// What corroborates the numeric assertion id this seam is willing to publish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AssertionIdCorroboration {
    /// The request that cites the certificate carries exactly one `Assertion`
    /// replay atom for the obligation, and that atom's id equals A. The ONLY
    /// corroboration.
    RequestAssertionAtom,
    /// Nothing corroborates A for this row. Nothing may be stamped — not A, not
    /// B, not a number derived from either, and not a payload's C.
    None,
}

impl AssertionIdCorroboration {
    /// Which corroboration one obligation's renderings supply.
    ///
    /// The bundle input gates have already refused every DISAGREEMENT, so this
    /// decides only whether corroboration is AVAILABLE, and it repeats the one
    /// comparison it relies on (E equals A) rather than trusting the gate for
    /// it.
    ///
    /// `index` supplies the one fact a single row cannot see: whether some OTHER
    /// obligation in the same bundle carries this number under a different
    /// identity. If it does, the number identifies neither and nothing is
    /// published for this row (see [`AssertionIdIndex`]).
    pub(crate) fn of(renderings: &AssertionIdRenderings, index: &AssertionIdIndex) -> Self {
        let Some(compiler_fact) = renderings.compiler_fact else {
            // Nothing to corroborate: the artifact seam already fails closed on
            // a missing assertion id.
            return Self::None;
        };
        if index.is_ambiguous(compiler_fact) {
            return Self::None;
        }
        // Exactly one atom, stating an id, equal to A. No atom, an atom with no
        // id, and two atoms (even agreeing ones) license nothing. B and the
        // payload's C are deliberately not consulted: see the module docs.
        match renderings.request_atoms.as_deref() {
            Some([Some(atom)]) if *atom == compiler_fact => Self::RequestAssertionAtom,
            _ => Self::None,
        }
    }

    /// The numeric id this corroboration licenses, if any.
    pub(crate) fn licensed(self, renderings: &AssertionIdRenderings) -> Option<u32> {
        match self {
            Self::None => None,
            Self::RequestAssertionAtom => renderings.compiler_fact,
        }
    }

    /// The INDEPENDENT numeric rendering, when one exists: the citing request's
    /// atom id.
    ///
    /// The row records it beside A so that the artifact-level cross-checks
    /// compare two independently sourced values instead of one field against
    /// itself. See
    /// [`crate::native_trust_ir_bundle::TrustVcNativeTrustIrCertificateEvidence::admit_native_proof_artifact`].
    pub(crate) fn independent(self, renderings: &AssertionIdRenderings) -> Option<u32> {
        match (self, renderings.request_atoms.as_deref()) {
            (Self::RequestAssertionAtom, Some([Some(atom)])) => Some(*atom),
            _ => None,
        }
    }
}

/// The `Assertion` replay atoms of one request's context that cite `obligation`.
fn assertion_atoms_for(
    context: &NativeReplayContext,
    obligation: ProofId,
) -> impl Iterator<Item = &NativeReplayAtom> {
    context.atoms.iter().filter(move |atom| {
        atom.kind == NativeReplayAtomKind::Assertion && atom.obligation == Some(obligation)
    })
}

/// THE BUNDLE INPUT GATE for assertion-id renderings.
///
/// Runs beside `validate_producer_module`: a bundle whose renderings disagree is
/// REFUSED, not reasoned about. Every check is producer-agnostic — it compares
/// renderings to each other and never to a derivation only one producer
/// performs (see the module docs).
pub(crate) fn validate_assertion_id_renderings(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
) -> Result<(), TrustEngineError> {
    let mut by_string: BTreeMap<String, (u32, u32)> = BTreeMap::new();
    for obligation in &module.proof_obligations {
        let source = compiler_facts.obligation_source(obligation.id);
        let renderings = AssertionIdRenderings::of(obligation, source);
        let obligation_id = obligation.id.index();

        // A rendering that is PRESENT and unreadable is not absent: defaulting
        // here would be fail-open. The rule applies where it has a subject, a
        // row that carries a numeric rendering A this seam could publish. With
        // no A the row publishes nothing whatever the payload says (an
        // unrequested row whose payload is not JSON does not refuse the whole
        // bundle), and a requested row whose payload cannot be read still
        // declines in the formula decoder. Such a payload is NOT ignored: it
        // might carry any number, so `AssertionIdIndex` withdraws every id the
        // bundle would publish (round 14).
        if let (Some(_), Some(reason)) = (
            renderings.compiler_fact,
            renderings.payload_unreadable.as_ref(),
        ) {
            return Err(
                TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                    module: module.name.clone(),
                    obligation_id,
                    reason: format!(
                    "a rendering of the assertion identity is present but unreadable ({reason}), \
                     and an unreadable rendering may not be treated as an absent one"
                ),
                    renderings: renderings.describe(),
                },
            );
        }

        // A vs C — two numeric renderings of one identity.
        if let (Some(compiler_fact), Some(payload_native)) =
            (renderings.compiler_fact, renderings.payload_native)
        {
            if compiler_fact != payload_native {
                return Err(
                    TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                        module: module.name.clone(),
                        obligation_id,
                        reason:
                            "the compiler-fact assertion id and the id embedded in the formula \
                             payload this lane decodes are two renderings of ONE identity and \
                             they differ"
                                .to_string(),
                        renderings: renderings.describe(),
                    },
                );
            }
        }

        // B vs D — two string renderings of one identity.
        if let (Some(obligation_source), Some(payload_source)) = (
            renderings.obligation_source.as_ref(),
            renderings.payload_source.as_ref(),
        ) {
            if obligation_source != payload_source {
                return Err(
                    TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                        module: module.name.clone(),
                        obligation_id,
                        reason:
                            "the obligation's own `source.assertion_id` and the one embedded in \
                             its formula payload are two renderings of ONE identity and they \
                             differ"
                                .to_string(),
                        renderings: renderings.describe(),
                    },
                );
            }
        }

        // Bundle-wide: B -> A must be a FUNCTION — one `source.assertion_id`
        // string may not carry two different numbers. That holds under any
        // derivation whatever, so a violation is a contradiction inside the
        // bundle and is refused here.
        //
        // The converse (two strings sharing one number) is NOT refused any more;
        // see [`AssertionIdIndex`] for why the producer's own derivation makes
        // that legitimate, and for the fail-closed handling that replaced the
        // refusal.
        let (Some(string), Some(numeric)) = (
            renderings.obligation_source.as_ref(),
            renderings.compiler_fact,
        ) else {
            continue;
        };
        if let Some((seen_numeric, seen_obligation)) = by_string.get(string) {
            if *seen_numeric != numeric {
                return Err(
                    TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                        module: module.name.clone(),
                        obligation_id,
                        reason: format!(
                            "obligation {seen_obligation} carries the same \
                         `source.assertion_id` {string:?} under compiler-fact assertion id \
                         {seen_numeric}, so the numeric rendering is not a function of the \
                         identity it re-encodes"
                        ),
                        renderings: renderings.describe(),
                    },
                );
            }
        }
        by_string.insert(string.clone(), (numeric, obligation_id));
    }
    Ok(())
}

/// THE BUNDLE INPUT GATE for rendering E: the replay atoms of every TrustVc
/// request.
///
/// Runs beside [`validate_assertion_id_renderings`], after trust-ir's own
/// validator. For every replay atom that cites an obligation it refuses the
/// bundle when the atom:
///
/// * cites an obligation the module does not carry, or one its request does
///   not list;
/// * carries an `assertion_id` other than that obligation's compiler-fact
///   number A (whatever the atom's kind);
/// * is an `Assertion` atom whose formula is not EXACTLY its obligation's
///   formula — schema, payload, rendering, sort and bindings. The request
///   digest covers an atom's formula text but not its bindings, and
///   trust-ir-build compares atom formulas only for a solver-result basis, so
///   for a kernel-replayed certificate this is the only check that sees an atom
///   asserting another formula;
/// * is a second `Assertion` atom for one obligation that disagrees with the
///   first about the id.
///
/// An atom that cites no obligation renders no obligation's identity and
/// licenses nothing, so it is left to trust-ir's validator, which refuses an
/// `Assertion` atom of that shape. Atoms of TrustMc and TrustWp requests are
/// never read here: only the request that cites a certificate can license its
/// id.
pub(crate) fn validate_request_assertion_atoms(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    requests: &[NativeVerificationRequest],
) -> Result<(), TrustEngineError> {
    let refuse = |obligation_id: ProofId,
                  reason: String,
                  renderings: String|
     -> Result<(), TrustEngineError> {
        Err(
            TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                module: module.name.clone(),
                obligation_id: obligation_id.index(),
                reason,
                renderings,
            },
        )
    };
    for request in requests {
        let NativeVerificationRequest::TrustVc(request) = request else {
            continue;
        };
        let request_id = request.id.index();
        let context = &request.provenance.replay_context;
        let mut first_assertion_atom: BTreeMap<ProofId, &NativeReplayAtom> = BTreeMap::new();
        for atom in &context.atoms {
            let Some(obligation_id) = atom.obligation else {
                continue;
            };
            let atom_label = format!(
                "TrustVc request {request_id}'s {:?} replay atom #{}",
                atom.kind,
                atom.id.index()
            );
            let Some(obligation) = module
                .proof_obligations
                .iter()
                .find(|obligation| obligation.id == obligation_id)
            else {
                return refuse(
                    obligation_id,
                    format!(
                        "{atom_label} cites an obligation the module does not carry, so the \
                         identity it renders belongs to nothing"
                    ),
                    "no such obligation".to_string(),
                );
            };
            let renderings = AssertionIdRenderings::cited_by(
                obligation,
                compiler_facts.obligation_source(obligation_id),
                context,
            );
            if !request.obligations.contains(&obligation_id) {
                return refuse(
                    obligation_id,
                    format!(
                        "{atom_label} cites an obligation its request does not list, so it \
                         states an identity for a certificate the request does not cite"
                    ),
                    renderings.describe(),
                );
            }
            if let Some(assertion_id) = atom.assertion_id {
                if renderings.compiler_fact != Some(assertion_id.index()) {
                    return refuse(
                        obligation_id,
                        format!(
                            "{atom_label} carries assertion id {} and the compiler fact \
                             carries another: two renderings of ONE identity that differ",
                            assertion_id.index()
                        ),
                        renderings.describe(),
                    );
                }
            }
            if atom.kind != NativeReplayAtomKind::Assertion {
                continue;
            }
            if obligation.formula.as_ref() != Some(&atom.formula) {
                return refuse(
                    obligation_id,
                    format!(
                        "{atom_label} asserts {:?} under schema `{}`, and its obligation \
                         states {}; the atom and the certificate's formula must be ONE \
                         formula, bindings included",
                        atom.formula.payload,
                        atom.formula.schema,
                        obligation.formula.as_ref().map_or_else(
                            || "no formula".to_string(),
                            |formula| format!(
                                "{:?} under schema `{}`",
                                formula.payload, formula.schema
                            )
                        ),
                    ),
                    renderings.describe(),
                );
            }
            if let Some(first) = first_assertion_atom.get(&obligation_id) {
                if first.assertion_id != atom.assertion_id {
                    return refuse(
                        obligation_id,
                        format!(
                            "{atom_label} and Assertion atom #{} both assert this obligation \
                             and disagree about its assertion id",
                            first.id.index()
                        ),
                        renderings.describe(),
                    );
                }
            } else {
                first_assertion_atom.insert(obligation_id, atom);
            }
        }
    }
    Ok(())
}

/// THE OBLIGATION KIND'S TWO RENDERINGS.
///
/// ROUND 9's second export-seam finding, and it is the blocker's shape one field
/// over. An obligation's KIND is decision-bearing here — it is what declines an
/// obligation as a def-site precondition and what dispatches every arm of
/// `callee_contract_facts` — and the bundle renders it TWICE:
///
/// * `module.proof_obligations[].kind` (`ObligationKind`), the one the lane
///   reads, published on the evidence row as `obligation_kind`;
/// * `compiler_facts.obligation_sources[].cause` (`NativeObligationCause`),
///   which this crate republishes inside `compiler_facts_binding.cause` and
///   folds into `obligation_source_digest`.
///
/// MEASURED (probe R9-P12): moving only the compiler-fact `cause` of the row
/// trust-vc PROVES to `Precondition` was ACCEPTED, and the published row then
/// said `obligation_kind = Postcondition` and `compiler_facts_binding.cause =
/// Precondition` at once, with the artifact admitted. Two renderings, one
/// checked, the other used — published.
///
/// WHAT THIS CHECKS, AND WHAT IT DELIBERATELY DOES NOT. The two vocabularies are
/// not in bijection: `NativeObligationCause` has compiler-side causes
/// (`BoundsCheck`, `OverflowCheck`, `CastCheck`, `Panic`, …) that several kinds
/// legitimately map onto, and `Other` is a legal cause for anything. Demanding a
/// total correspondence would refuse bundles upstream considers well-formed —
/// the mistake round 8 made with the assertion-id injection rule. So only the
/// FLAT CONTRADICTIONS are refused: a `Precondition` whose cause says
/// `Postcondition`, and a `Postcondition` whose cause says `Precondition`.
/// Nothing legitimate calls one obligation both, and those two are exactly the
/// pair that decides whether a row is a callee contract.
pub(crate) fn validate_obligation_kind_renderings(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
) -> Result<(), TrustEngineError> {
    for obligation in &module.proof_obligations {
        let Some(source) = compiler_facts.obligation_source(obligation.id) else {
            continue;
        };
        let contradicted = matches!(
            (&obligation.kind, source.cause),
            (
                ObligationKind::Precondition,
                NativeObligationCause::Postcondition
            ) | (
                ObligationKind::Postcondition,
                NativeObligationCause::Precondition
            )
        );
        if contradicted {
            return Err(
                TrustEngineError::NativeTrustIrObligationKindRenderingsDisagree {
                    module: module.name.clone(),
                    obligation_id: obligation.id.index(),
                    kind: format!("{:?}", obligation.kind),
                    cause: format!("{:?}", source.cause),
                },
            );
        }
    }
    Ok(())
}

/// What the export seam may stamp for one obligation, cited by the request
/// whose replay context is `request_context`.
///
/// The gates above have already refused every DISAGREEMENT in the bundle, so
/// this decides only which corroboration is available — and refuses to stamp
/// when none is.
pub(crate) fn corroboration_for(
    obligations: &BTreeMap<ProofId, &ProofObligation>,
    sources: &BTreeMap<ProofId, &NativeObligationSource>,
    index: &AssertionIdIndex,
    obligation_id: ProofId,
    request_context: &NativeReplayContext,
) -> (AssertionIdRenderings, AssertionIdCorroboration) {
    let Some(obligation) = obligations.get(&obligation_id).copied() else {
        return (
            AssertionIdRenderings::default(),
            AssertionIdCorroboration::None,
        );
    };
    let renderings = AssertionIdRenderings::cited_by(
        obligation,
        sources.get(&obligation_id).copied(),
        request_context,
    );
    let corroboration = AssertionIdCorroboration::of(&renderings, index);
    (renderings, corroboration)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::request::{NativeAssertionId, NativeReplayAtomId, NativeVerificationBundle};
    use trust_ir::{
        NativeObligationCause, ObligationKind, ProofFormula, ProofObligation,
        ProofObligationSourceIdentity, ProofStatus,
    };

    fn obligation(assertion_id: Option<&str>, payload: Option<&str>) -> ProofObligation {
        let mut obligation = ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "probe",
        );
        obligation.source = assertion_id
            .map(|assertion_id| ProofObligationSourceIdentity::new("probe", assertion_id));
        obligation.formula = payload.map(|payload| ProofFormula {
            schema: TRUST_TYPES_FORMULA_SCHEMA_V1.to_string(),
            payload: payload.to_string(),
            smtlib: None,
            sort: None,
            bindings: Vec::new(),
        });
        obligation
    }

    fn compiler_source(assertion_id: Option<u32>) -> NativeObligationSource {
        NativeObligationSource {
            obligation: ProofId::new(1),
            public_obligation_id: "vc:probe:postcondition:0".to_string(),
            function: None,
            span: None,
            assertion_id: assertion_id.map(NativeAssertionId::new),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: Vec::new(),
        }
    }

    /// THE `None` ARM, exercised directly: it is unreachable through the bundle
    /// path (upstream refuses an obligation with no embedded source identity —
    /// pinned in `tests/native_trust_ir_bundle.rs`), so it is tested here.
    #[test]
    fn a_compiler_fact_id_with_no_other_rendering_is_uncorroborated() {
        let obligation = obligation(None, None);
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(corroboration, AssertionIdCorroboration::None);
        assert_eq!(corroboration.licensed(&renderings), None);
        assert_eq!(corroboration.independent(&renderings), None);
    }

    /// A payload that renders the id a second time (rendering C, agreeing with
    /// A) licenses NOTHING: such a payload is a JSON document, not an SMT-LIB
    /// text, so trust-ir never replays its certificate. It is read only so that
    /// a disagreeing one refuses the bundle.
    #[test]
    fn a_payload_rendering_of_the_id_licenses_nothing() {
        let obligation = obligation(
            Some("rust-assertion:1"),
            Some(
                r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:1","native_assertion_id":9}}"#,
            ),
        );
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(renderings.payload_native, Some(9), "C is read");
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(corroboration, AssertionIdCorroboration::None);
        assert_eq!(corroboration.licensed(&renderings), None);
        assert_eq!(corroboration.independent(&renderings), None);
    }

    /// No second numeric rendering, but the obligation's own string identity is
    /// there.
    ///
    /// It corroborates NOTHING: "the bundle-wide B -> A map is a function" is
    /// invariant under any relabeling of the numbers, so it cannot say which
    /// assertion a number names. Nothing is published for this row.
    #[test]
    fn the_string_rendering_alone_corroborates_nothing() {
        let obligation = obligation(Some("rust-assertion:1"), None);
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(
            renderings.obligation_source.as_deref(),
            Some("rust-assertion:1"),
            "the string rendering IS present; it is simply not corroboration"
        );
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(corroboration, AssertionIdCorroboration::None);
        assert_eq!(corroboration.licensed(&renderings), None);
        assert_eq!(corroboration.independent(&renderings), None);
    }

    /// THE RELABELING ARGUMENT, MECHANIZED. Every numeric rendering in the
    /// bundle is replaced by a different number under an injective map. The old
    /// `BundleStringMap` grade licensed BOTH labellings, which is exactly why it
    /// was not corroboration: a grade that accepts a value and its relabeling
    /// says nothing about the value.
    #[test]
    fn a_relabeling_of_every_number_is_indistinguishable_to_the_string_map() {
        let relabel = |value: u32| value.wrapping_mul(7).wrapping_add(13);
        for original in [0u32, 1, 9, 4242] {
            let obligation = obligation(Some("rust-assertion:1"), None);
            let source = compiler_source(Some(original));
            let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
            let relabelled_source = compiler_source(Some(relabel(original)));
            let relabelled = AssertionIdRenderings::of(&obligation, Some(&relabelled_source));
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
                AssertionIdCorroboration::of(&relabelled, &AssertionIdIndex::default()),
                "the grade cannot tell {original} from {}",
                relabel(original)
            );
            // And, since it cannot tell them apart, it may license NEITHER.
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default())
                    .licensed(&renderings),
                None
            );
        }
    }

    /// A payload under the decoded schema whose `source` key is ABSENT is an
    /// explicit state, not a silent downgrade.
    #[test]
    fn a_payload_with_no_source_block_says_so() {
        let obligation = obligation(
            Some("rust-assertion:1"),
            Some(r#"{"formula":{"Bool":true}}"#),
        );
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(renderings.payload_source_block, PayloadSourceBlock::Absent);
        assert_eq!(renderings.payload_native, None);
        assert_eq!(renderings.payload_unreadable, None);
        assert!(
            renderings
                .describe()
                .contains("payload carries no `source` block"),
            "the absence must be NAMED: {}",
            renderings.describe()
        );
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// A `source` key that is not an object is PRESENT and unreadable, so it
    /// fails closed as a refusal rather than being read as an absence.
    #[test]
    fn a_payload_source_that_is_not_an_object_is_unreadable() {
        for payload in [
            r#"{"formula":{"Bool":true},"source":5}"#,
            r#"{"formula":{"Bool":true},"source":"rust-assertion:1"}"#,
            r#"{"formula":{"Bool":true},"source":[{"native_assertion_id":9}]}"#,
            r#"{"formula":{"Bool":true},"source":null}"#,
        ] {
            let obligation = obligation(Some("rust-assertion:1"), Some(payload));
            let source = compiler_source(Some(9));
            let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::NotAnObject,
                "{payload}"
            );
            assert!(
                renderings.payload_unreadable.is_some(),
                "a present-but-unreadable rendering may not read as absent: {payload}"
            );
            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(source);
            validate_assertion_id_renderings(&module, &facts)
                .expect_err("an unreadable rendering must refuse the bundle");
        }
    }

    /// The producer's OTHER payload shape renders the identity too. It is read,
    /// and like the nested shape it licenses nothing.
    #[test]
    fn the_top_level_source_record_is_read_and_licenses_nothing() {
        let mut obligation = obligation(Some("rust-assertion:1"), Some("{}"));
        let formula = obligation.formula.as_mut().expect("formula");
        formula.schema = TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1.to_string();
        // Exactly `trust-ir-bridge`'s `source_json()`: the WHOLE payload.
        formula.payload = r#"{"source_id":"mir-assert:probe:bb0:0","assertion_id":"rust-assertion:1","native_assertion_id":9,"span":{"file":"probe.rs","line_start":1,"col_start":1,"line_end":1,"col_end":2}}"#.to_string();
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(
            renderings.payload_source_block,
            PayloadSourceBlock::TopLevelObject
        );
        assert_eq!(renderings.payload_native, Some(9));
        assert_eq!(
            renderings.payload_source.as_deref(),
            Some("rust-assertion:1")
        );
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(corroboration, AssertionIdCorroboration::None);
        assert_eq!(corroboration.licensed(&renderings), None);
        assert_eq!(corroboration.independent(&renderings), None);
    }

    /// And it is a REAL cross-check, not a second reading of the same field:
    /// moving the compiler fact alone is refused by the bundle input gate.
    #[test]
    fn a_top_level_source_record_that_disagrees_refuses_the_bundle() {
        let mut obligation = obligation(Some("rust-assertion:1"), Some("{}"));
        let formula = obligation.formula.as_mut().expect("formula");
        formula.schema = TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1.to_string();
        formula.payload =
            r#"{"assertion_id":"rust-assertion:1","native_assertion_id":9}"#.to_string();
        let source = compiler_source(Some(4242));
        let mut module = Module::new("probe");
        module.proof_obligations.push(obligation);
        let mut facts = NativeCompilerFacts::default();
        facts.obligation_sources.push(source);
        let error = validate_assertion_id_renderings(&module, &facts)
            .expect_err("two numeric renderings of one identity that differ must refuse");
        assert!(
            format!("{error}").contains("4242"),
            "the refusal names what it saw: {error}"
        );
    }

    /// The top-level shape's present-but-unreadable state: the document under
    /// that schema IS the source record, so a non-object document fails closed
    /// exactly as a non-object `source` key does one level down.
    #[test]
    fn a_top_level_payload_that_is_not_an_object_is_unreadable() {
        for payload in ["5", r#""rust-assertion:1""#, "[]", "null"] {
            let mut obligation = obligation(Some("rust-assertion:1"), Some("{}"));
            let formula = obligation.formula.as_mut().expect("formula");
            formula.schema = TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1.to_string();
            formula.payload = payload.to_string();
            let source = compiler_source(Some(9));
            let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::TopLevelNotAnObject,
                "{payload}"
            );
            assert!(renderings.payload_unreadable.is_some(), "{payload}");
            assert!(
                renderings
                    .describe()
                    .contains("payload document is not an object"),
                "the state must be NAMED: {}",
                renderings.describe()
            );
            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(source);
            validate_assertion_id_renderings(&module, &facts)
                .expect_err("an unreadable rendering must refuse the bundle");
        }
    }

    /// A top-level source record that renders no number corroborates nothing —
    /// the shape is read, and reading it is not the same as finding something.
    #[test]
    fn a_top_level_source_record_with_no_number_corroborates_nothing() {
        let mut obligation = obligation(Some("rust-assertion:1"), Some("{}"));
        let formula = obligation.formula.as_mut().expect("formula");
        formula.schema = TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1.to_string();
        formula.payload = r#"{"assertion_id":"rust-assertion:1"}"#.to_string();
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(
            renderings.payload_source_block,
            PayloadSourceBlock::TopLevelObject
        );
        assert_eq!(renderings.payload_native, None);
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// A payload under a schema this seam does not know carries no renderings —
    /// it is not parsed, and nothing is inferred from its bytes.
    #[test]
    fn an_unknown_payload_schema_yields_no_payload_renderings() {
        let mut obligation = obligation(Some("rust-assertion:1"), Some("{}"));
        obligation.formula.as_mut().expect("formula").schema = "some-other-schema@3".to_string();
        obligation.formula.as_mut().expect("formula").payload =
            r#"{"source":{"native_assertion_id":404}}"#.to_string();
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(renderings.payload_native, None);
        assert_eq!(renderings.payload_unreadable, None);
        assert_eq!(
            renderings.payload_source_block,
            PayloadSourceBlock::NotDecoded,
            "an unknown schema is not a payload this seam read"
        );
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// The upstream conformance corpus bundle, whose TrustVc request 0 cites
    /// obligation 0 (compiler-fact number 1, formula `(>= 5 0)`), with that
    /// request given the atom Trust's `trust-ir-bridge` writes
    /// (`native_replay_context`): an `Assertion` atom citing the obligation,
    /// stating its formula cloned, carrying its compiler-fact number.
    fn corpus_with_bridge_atom() -> NativeVerificationBundle {
        let mut bundle: NativeVerificationBundle = serde_json::from_str(include_str!(
            "../fixtures/trust_ir_native/native_request_trust_bundle.json"
        ))
        .expect("the checked-in corpus bundle decodes");
        let obligation = bundle.module.proof_obligations[0].clone();
        let atom = NativeReplayAtom::assertion(
            NativeReplayAtomId::new(0),
            obligation
                .formula
                .clone()
                .expect("corpus obligation 0 states a formula"),
        )
        .with_obligation(obligation.id)
        .with_assertion_id(NativeAssertionId::new(1));
        trust_vc_context(&mut bundle).atoms.push(atom);
        bundle
    }

    fn trust_vc_context(bundle: &mut NativeVerificationBundle) -> &mut NativeReplayContext {
        let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
            panic!("the corpus's request 0 is its TrustVc request");
        };
        &mut request.provenance.replay_context
    }

    fn gate(bundle: &NativeVerificationBundle) -> Result<(), TrustEngineError> {
        validate_request_assertion_atoms(&bundle.module, &bundle.compiler_facts, &bundle.requests)
    }

    /// Rendering E as the evidence row reads it for obligation 0 of `bundle`,
    /// cited by request 0.
    fn row_renderings(bundle: &mut NativeVerificationBundle) -> AssertionIdRenderings {
        let obligation = bundle.module.proof_obligations[0].clone();
        let source = bundle
            .compiler_facts
            .obligation_source(obligation.id)
            .cloned();
        AssertionIdRenderings::cited_by(&obligation, source.as_ref(), trust_vc_context(bundle))
    }

    /// CONTROL. The bridge's atom passes the gate, and it is the corroboration:
    /// the row publishes A and records the atom's id as the independent
    /// rendering.
    #[test]
    fn the_citing_requests_assertion_atom_licenses_its_id() {
        let mut bundle = corpus_with_bridge_atom();
        gate(&bundle).expect("the bridge's atom agrees with its obligation");
        let renderings = row_renderings(&mut bundle);
        assert_eq!(renderings.request_atoms, Some(vec![Some(1)]));
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(
            corroboration,
            AssertionIdCorroboration::RequestAssertionAtom
        );
        assert_eq!(corroboration.licensed(&renderings), Some(1));
        assert_eq!(corroboration.independent(&renderings), Some(1));
    }

    /// LIAR L1: the atom's id forged. trust-ir refuses it at the door
    /// (`ReplayAtomAssertionMismatch`); this drives trust-vc's own check, so the
    /// refusal does not depend on trust-ir's.
    #[test]
    fn a_forged_atom_id_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        trust_vc_context(&mut bundle).atoms[0].assertion_id = Some(NativeAssertionId::new(2));
        let error = gate(&bundle).expect_err("a forged atom id must refuse the bundle");
        assert!(
            error.to_string().contains("carries assertion id 2"),
            "{error}"
        );
        // Even past the gate, the row licenses nothing for a disagreeing atom.
        let renderings = row_renderings(&mut bundle);
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// LIAR L2: the compiler fact forged, the atom kept.
    #[test]
    fn a_forged_compiler_fact_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(7));
        let error = gate(&bundle).expect_err("a forged compiler fact must refuse the bundle");
        assert!(error.to_string().contains("= 7"), "{error}");
    }

    /// LIAR L3: the atom asserts another formula than its obligation states.
    /// trust-ir-build compares atom formulas only for a solver-result basis, so
    /// for a kernel-replayed certificate this is the only check that sees it.
    #[test]
    fn an_atom_asserting_another_formula_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        let atom = &mut trust_vc_context(&mut bundle).atoms[0];
        atom.formula.payload = "(>= 0 5)".to_string();
        atom.formula.smtlib = Some("(>= 0 5)".to_string());
        atom.payload_digest = atom.expected_payload_digest();
        let error = gate(&bundle).expect_err("an atom asserting another formula must refuse");
        assert!(error.to_string().contains("(>= 0 5)"), "{error}");
    }

    /// The same formula text under another schema is another formula.
    #[test]
    fn an_atom_stating_the_text_under_another_schema_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        trust_vc_context(&mut bundle).atoms[0].formula.schema =
            TRUST_TYPES_FORMULA_SCHEMA_V1.to_string();
        gate(&bundle).expect_err("a formula under another schema is another formula");
    }

    /// Two `Assertion` atoms for one obligation that disagree about the id: one
    /// states it and one does not.
    #[test]
    fn two_atoms_that_disagree_about_the_id_refuse_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        let context = trust_vc_context(&mut bundle);
        let mut second = context.atoms[0].clone();
        second.id = NativeReplayAtomId::new(1);
        second.assertion_id = None;
        context.atoms.push(second);
        let error = gate(&bundle).expect_err("disagreeing atoms must refuse the bundle");
        assert!(error.to_string().contains("disagree"), "{error}");
    }

    /// Two atoms that agree pass the gate, and still license nothing: the row
    /// needs exactly one.
    #[test]
    fn two_agreeing_atoms_license_nothing() {
        let mut bundle = corpus_with_bridge_atom();
        let context = trust_vc_context(&mut bundle);
        let mut second = context.atoms[0].clone();
        second.id = NativeReplayAtomId::new(1);
        context.atoms.push(second);
        gate(&bundle).expect("agreeing atoms are not a contradiction");
        let renderings = row_renderings(&mut bundle);
        assert_eq!(renderings.request_atoms, Some(vec![Some(1), Some(1)]));
        let corroboration = AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default());
        assert_eq!(corroboration, AssertionIdCorroboration::None);
        assert_eq!(corroboration.licensed(&renderings), None);
    }

    /// An atom that states no id licenses none.
    #[test]
    fn an_atom_with_no_id_licenses_nothing() {
        let mut bundle = corpus_with_bridge_atom();
        trust_vc_context(&mut bundle).atoms[0].assertion_id = None;
        gate(&bundle).expect("an atom need not state an id");
        let renderings = row_renderings(&mut bundle);
        assert_eq!(renderings.request_atoms, Some(vec![None]));
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// An `Assumption` atom is a premise, not the certificate's goal: it
    /// licenses nothing even when it carries the right number.
    #[test]
    fn an_assumption_atom_licenses_nothing() {
        let mut bundle = corpus_with_bridge_atom();
        let atom = &mut trust_vc_context(&mut bundle).atoms[0];
        atom.kind = NativeReplayAtomKind::Assumption;
        atom.payload_digest = atom.expected_payload_digest();
        gate(&bundle).expect("its id is the obligation's own");
        let renderings = row_renderings(&mut bundle);
        assert_eq!(renderings.request_atoms, Some(Vec::new()));
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// An atom citing an obligation its request does not list states an id for
    /// a certificate the request does not cite.
    #[test]
    fn an_atom_citing_an_unlisted_obligation_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        let other = bundle.module.proof_obligations[2].clone();
        let atom = &mut trust_vc_context(&mut bundle).atoms[0];
        atom.obligation = Some(other.id);
        atom.formula = other.formula.expect("corpus obligation 2 states a formula");
        atom.assertion_id = Some(NativeAssertionId::new(0));
        atom.payload_digest = atom.expected_payload_digest();
        let error = gate(&bundle).expect_err("an atom for an unlisted obligation must refuse");
        assert!(error.to_string().contains("does not list"), "{error}");
    }

    /// An atom citing an obligation the module does not carry.
    #[test]
    fn an_atom_citing_an_unknown_obligation_refuses_the_bundle() {
        let mut bundle = corpus_with_bridge_atom();
        trust_vc_context(&mut bundle).atoms[0].obligation = Some(ProofId::new(4242));
        let error = gate(&bundle).expect_err("an atom for no obligation must refuse");
        assert!(error.to_string().contains("does not carry"), "{error}");
    }

    /// A number two assertion identities share names neither, atom or not.
    #[test]
    fn an_ambiguous_number_is_licensed_by_no_atom() {
        let mut bundle = corpus_with_bridge_atom();
        let renderings = row_renderings(&mut bundle);
        let index = AssertionIdIndex {
            ambiguous: BTreeSet::from([1]),
            unreadable: None,
        };
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &index),
            AssertionIdCorroboration::None
        );
    }

    fn index(bundle: &NativeVerificationBundle) -> AssertionIdIndex {
        AssertionIdIndex::of(&bundle.module, &bundle.compiler_facts, &bundle.requests)
    }

    /// Gives each of `obligations` the assertion identity (`string`, `number`):
    /// its `source.assertion_id`, its compiler fact, and the id of every
    /// TrustVc atom citing it. The integration tests reseal the same edit;
    /// the index and the gates read no digest, so this does not.
    fn relabel(
        bundle: &mut NativeVerificationBundle,
        obligations: &[usize],
        string: &str,
        number: u32,
    ) {
        for &position in obligations {
            let obligation = &mut bundle.module.proof_obligations[position];
            obligation
                .source
                .as_mut()
                .expect("corpus obligations carry a source identity")
                .assertion_id = string.to_string();
            let obligation_id = obligation.id;
            for source in &mut bundle.compiler_facts.obligation_sources {
                if source.obligation == obligation_id {
                    source.assertion_id = Some(NativeAssertionId::new(number));
                }
            }
            for atom in &mut trust_vc_context(bundle).atoms {
                if atom.obligation == Some(obligation_id) && atom.assertion_id.is_some() {
                    atom.assertion_id = Some(NativeAssertionId::new(number));
                }
            }
        }
    }

    /// Obligation 0 takes obligation `victim`'s whole identity: its string, its
    /// number, and that number on the atom.
    fn steal(bundle: &mut NativeVerificationBundle, victim: usize) -> u32 {
        let string = bundle.module.proof_obligations[victim]
            .source
            .as_ref()
            .expect("corpus obligations carry a source identity")
            .assertion_id
            .clone();
        let number = bundle
            .compiler_facts
            .obligation_source(bundle.module.proof_obligations[victim].id)
            .and_then(|source| source.assertion_id)
            .expect("corpus obligations carry a compiler-fact number")
            .index();
        relabel(bundle, &[0], &string, number);
        number
    }

    /// CONTROL. In the corpus with the bridge's atom, every number names one
    /// obligation. The TrustWp request's atom for obligation 2 states 0, which
    /// obligation 2's own compiler fact carries: one obligation, one identity.
    #[test]
    fn the_corpus_numbers_are_unambiguous() {
        let bundle = corpus_with_bridge_atom();
        let index = index(&bundle);
        for number in [0, 1, 2] {
            assert!(!index.is_ambiguous(number), "{number}");
        }
    }

    /// LIAR (round 13 blocker): obligation 0 steals obligation 1's or
    /// obligation 2's whole identity. Every gate passes: the strings agree with
    /// the numbers, B -> A is a function, and the atom equals the fact. The
    /// strings-only index therefore licensed the stolen number. Two obligations
    /// with different formulas and public ids now carry it, so it names neither.
    #[test]
    fn a_stolen_identity_is_ambiguous() {
        for victim in [1, 2] {
            let mut bundle = corpus_with_bridge_atom();
            let stolen = steal(&mut bundle, victim);
            validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
                .expect("the gates see no disagreement");
            gate(&bundle).expect("the atom equals its fact");
            let renderings = row_renderings(&mut bundle);
            assert_eq!(renderings.compiler_fact, Some(stolen));
            assert_eq!(renderings.request_atoms, Some(vec![Some(stolen)]));
            let index = index(&bundle);
            assert!(index.is_ambiguous(stolen), "victim {victim}");
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &index),
                AssertionIdCorroboration::None,
                "victim {victim}"
            );
        }
    }

    /// LIAR (round 13 variant): obligations 0 and 1 both relabeled to one fresh
    /// identity. One string, one number, two formulas.
    #[test]
    fn one_fresh_identity_on_two_obligations_is_ambiguous() {
        let mut bundle = corpus_with_bridge_atom();
        relabel(&mut bundle, &[0, 1], "rust-assertion:9", 9);
        validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
            .expect("the gates see no disagreement");
        gate(&bundle).expect("the atom equals its fact");
        let renderings = row_renderings(&mut bundle);
        let index = index(&bundle);
        assert!(index.is_ambiguous(9));
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &index),
            AssertionIdCorroboration::None
        );
    }

    /// A number only an ATOM gives another obligation is still carried by it.
    /// Obligation 2 loses its compiler fact (so trust-ir checks no atom id
    /// against one), and the TrustWp request's atom for it states obligation
    /// 0's number 1.
    #[test]
    fn a_number_an_atom_of_another_request_gives_another_obligation_is_ambiguous() {
        let mut bundle = corpus_with_bridge_atom();
        let obligation_2 = bundle.module.proof_obligations[2].id;
        bundle
            .compiler_facts
            .obligation_sources
            .retain(|source| source.obligation != obligation_2);
        let NativeVerificationRequest::TrustWp(trust_wp) = &mut bundle.requests[4] else {
            panic!("the corpus's request 4 is a TrustWp request");
        };
        for atom in &mut trust_wp.provenance.replay_context.atoms {
            if atom.assertion_id.is_some() {
                atom.assertion_id = Some(NativeAssertionId::new(1));
            }
        }
        assert!(index(&bundle).is_ambiguous(1));
    }

    /// A number only a PAYLOAD gives another obligation is still carried by it:
    /// obligation 2, with no compiler fact, renders obligation 0's number 1 in
    /// its payload's source record.
    #[test]
    fn a_number_a_payload_gives_another_obligation_is_ambiguous() {
        let mut bundle = corpus_with_bridge_atom();
        let obligation_2 = bundle.module.proof_obligations[2].id;
        bundle
            .compiler_facts
            .obligation_sources
            .retain(|source| source.obligation != obligation_2);
        let formula = bundle.module.proof_obligations[2]
            .formula
            .as_mut()
            .expect("corpus obligation 2 states a formula");
        formula.schema = TRUST_TYPES_FORMULA_SCHEMA_V1.to_string();
        formula.payload =
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1}}"#.to_string();
        assert!(index(&bundle).is_ambiguous(1));
    }

    /// Adds obligation 7, a clone of obligation 2 with its own public id and
    /// string (`vc:checked_add:assert:7`, `rust-assertion:7`), no compiler fact,
    /// listed by no request, whose formula is `payload` under `schema`: the
    /// round-14 review's carrier.
    fn add_unrequested_factless_obligation(
        bundle: &mut NativeVerificationBundle,
        schema: &str,
        payload: &str,
    ) {
        let mut extra = bundle.module.proof_obligations[2].clone();
        extra.id = ProofId::new(7);
        let source = extra
            .source
            .as_mut()
            .expect("corpus obligations carry a source identity");
        if let Some(public) = source.public.as_mut() {
            public.obligation_id = "vc:checked_add:assert:7".to_string();
        }
        source.assertion_id = "rust-assertion:7".to_string();
        let formula = extra
            .formula
            .as_mut()
            .expect("corpus obligation 2 states a formula");
        formula.schema = schema.to_string();
        formula.payload = payload.to_string();
        formula.smtlib = None;
        bundle.module.proof_obligations.push(extra);
    }

    /// Obligation 0's number spelled UNREADABLY by an unrequested obligation
    /// with no compiler fact, in both payload shapes. Each might carry any
    /// number, so each withdraws every license.
    const UNREADABLE_CARRIERS: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
            "C as the string \"1\"",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1.0}}"#,
            "C as the float 1.0",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":4294967297}}"#,
            "C as 2^32 + 1, which truncates to 1 as a u32",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"#,
            "a truncated payload that is not JSON",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":"native_assertion_id=1"}"#,
            "a source block that is not an object",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"assertion_id":7}}"#,
            "D as a number, not a string",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":"1","assertion_id":"rust-assertion:7"}"#,
            "top-level C as the string \"1\"",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":1.0,"assertion_id":"rust-assertion:7"}"#,
            "top-level C as the float 1.0",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":4294967297,"assertion_id":"rust-assertion:7"}"#,
            "top-level C as 2^32 + 1",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#""native_assertion_id=1""#,
            "a top-level document that is not an object",
        ),
    ];

    /// CONTROL for the liar below: the same carrier with a READABLE number.
    /// Obligation 0's number 1 written as a `u32` is counted and ambiguous, and
    /// only 1 is; an unused readable number takes nothing from obligation 0.
    #[test]
    fn a_readable_carrier_withdraws_only_its_own_number() {
        for schema in [
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
        ] {
            let payload = |number: u32| {
                if schema == TRUST_TYPES_FORMULA_SCHEMA_V1 {
                    format!(
                        r#"{{"formula":{{"Bool":true}},"source":{{"native_assertion_id":{number}}}}}"#
                    )
                } else {
                    format!(
                        r#"{{"native_assertion_id":{number},"assertion_id":"rust-assertion:7"}}"#
                    )
                }
            };
            let mut bundle = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut bundle, schema, &payload(1));
            let ids = index(&bundle);
            assert_eq!(ids.unreadable(), None, "{schema}");
            assert!(ids.is_ambiguous(1), "{schema}");
            assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(2), "{schema}");

            let mut bundle = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut bundle, schema, &payload(7));
            let ids = index(&bundle);
            assert!(!ids.is_ambiguous(1), "{schema}");
            let renderings = row_renderings(&mut bundle);
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &ids).licensed(&renderings),
                Some(1),
                "{schema}"
            );
        }
    }

    /// LIAR (round 14): an unrequested obligation with no compiler fact spells
    /// obligation 0's number unreadably. The old index counted only numbers
    /// that read as a `u32`, so this obligation was no carrier and obligation 0
    /// was licensed 1 while the same number written as a `u32` was refused. The
    /// bundle input gate does not refuse it (no A beside it), so the index now
    /// withdraws every number.
    #[test]
    fn an_unreadable_carrier_withdraws_every_number() {
        for (schema, payload, label) in UNREADABLE_CARRIERS {
            let mut bundle = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut bundle, schema, payload);
            validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
                .unwrap_or_else(|error| panic!("{label}: no A, so no bundle refusal: {error}"));
            gate(&bundle).unwrap_or_else(|error| panic!("{label}: {error}"));
            let ids = index(&bundle);
            assert!(
                ids.unreadable()
                    .is_some_and(|reason| reason.contains("obligation 7")),
                "{label}: {ids:?}"
            );
            for number in [0, 1, 2, 7, 9, u32::MAX] {
                assert!(ids.is_ambiguous(number), "{label}: {number}");
            }
            let renderings = row_renderings(&mut bundle);
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &ids),
                AssertionIdCorroboration::None,
                "{label}"
            );
        }
    }

    /// Payloads in which one object states a key twice (round 15), in both
    /// payload shapes. `serde_json::Value` keeps the LAST value of a repeated
    /// key, so each of these used to read as whatever came last.
    const REPEATED_KEY_PAYLOADS: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1","native_assertion_id":7}}"#,
            "an unreadable C hidden by a later readable 7",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1,"native_assertion_id":7}}"#,
            "C twice, 1 then 7",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"source":{"native_assertion_id":7}}"#,
            "the source block twice, 1 then 7",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"source":{}}"#,
            "the source block twice, 1 then empty",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":1,"native_assertion_id":7,"assertion_id":"rust-assertion:7"}"#,
            "top-level C twice, 1 then 7",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1,"native\u005fassertion_id":7}}"#,
            "C twice, the second key spelled with an escape",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:7","assertion_id":"rust-assertion:1","native_assertion_id":7}}"#,
            "D twice",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true,"Bool":false},"source":{"native_assertion_id":7}}"#,
            "a key repeated outside the source record",
        ),
    ];

    /// LIAR (round 15): a document with a repeated key has no single reading,
    /// so it is UNREADABLE, never read as its last value. Beside an A it
    /// refuses the bundle.
    #[test]
    fn a_payload_that_repeats_a_key_is_unreadable() {
        for (schema, payload, label) in REPEATED_KEY_PAYLOADS {
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::RepeatedKey,
                "{label}"
            );
            assert_eq!(renderings.payload_native, None, "{label}");
            assert_eq!(renderings.payload_source, None, "{label}");
            assert!(
                renderings
                    .payload_unreadable
                    .as_deref()
                    .is_some_and(|reason| reason.contains("repeats a key")),
                "{label}: {renderings:?}"
            );
            assert!(
                renderings
                    .describe()
                    .contains("payload repeats a key inside one JSON object"),
                "{label}: the state must be NAMED: {}",
                renderings.describe()
            );
            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(compiler_source(Some(7)));
            validate_assertion_id_renderings(&module, &facts)
                .expect_err("a repeated key beside an A must refuse the bundle");
        }
    }

    /// CONTROL: one key in two DIFFERENT objects is not a repeat. The check is
    /// per object, so a predicate with two `Bool` leaves beside a source record
    /// reads as before.
    #[test]
    fn one_key_in_two_objects_is_not_a_repeat() {
        let obligation = obligation(
            Some("rust-assertion:1"),
            Some(
                r#"{"formula":{"And":[{"Bool":true},{"Bool":false}]},"source":{"assertion_id":"rust-assertion:1","native_assertion_id":9}}"#,
            ),
        );
        let source = compiler_source(Some(9));
        let renderings = AssertionIdRenderings::of(&obligation, Some(&source));
        assert_eq!(renderings.payload_source_block, PayloadSourceBlock::Object);
        assert_eq!(renderings.payload_unreadable, None);
        assert_eq!(renderings.payload_native, Some(9));
        let mut module = Module::new("probe");
        module.proof_obligations.push(obligation);
        let mut facts = NativeCompilerFacts::default();
        facts.obligation_sources.push(source);
        validate_assertion_id_renderings(&module, &facts).expect("nothing repeats in one object");
    }

    /// LIAR (round 15): the round-14 carrier plus one repeated key. Obligation
    /// 7 (no compiler fact, requested by nobody) renders obligation 0's number
    /// and then a harmless 7 under the same key; a last-wins reader counted
    /// only 7, and obligation 0 was licensed 1. The same payload on a replay
    /// atom's formula is read the same way.
    #[test]
    fn a_repeated_key_withdraws_every_number() {
        for (schema, payload, label) in REPEATED_KEY_PAYLOADS {
            let mut bundle = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut bundle, schema, payload);
            validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
                .unwrap_or_else(|error| panic!("{label}: no A, so no bundle refusal: {error}"));
            gate(&bundle).unwrap_or_else(|error| panic!("{label}: {error}"));
            let ids = index(&bundle);
            assert!(
                ids.unreadable()
                    .is_some_and(|reason| reason.contains("obligation 7")
                        && reason.contains("repeats a key")),
                "{label}: {ids:?}"
            );
            for number in [0, 1, 2, 7, 9, u32::MAX] {
                assert!(ids.is_ambiguous(number), "{label}: {number}");
            }
            let renderings = row_renderings(&mut bundle);
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &ids),
                AssertionIdCorroboration::None,
                "{label}"
            );
        }

        let mut bundle = corpus_with_bridge_atom();
        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1","native_assertion_id":7}}"#,
        );
        let ids = index(&bundle);
        assert!(
            ids.unreadable()
                .is_some_and(|reason| reason.contains("replay atom")),
            "{ids:?}"
        );
        assert!(ids.is_ambiguous(1));
    }

    /// Gives the first `Assumption` atom of the TrustWp request 4 (it cites
    /// obligation 2) the formula `payload` under the nested payload schema.
    fn set_trust_wp_assumption_formula(bundle: &mut NativeVerificationBundle, payload: &str) {
        set_trust_wp_assumption_formula_under(bundle, TRUST_TYPES_FORMULA_SCHEMA_V1, payload);
    }

    /// [`set_trust_wp_assumption_formula`] with the payload under `schema`.
    fn set_trust_wp_assumption_formula_under(
        bundle: &mut NativeVerificationBundle,
        schema: &str,
        payload: &str,
    ) {
        let NativeVerificationRequest::TrustWp(trust_wp) = &mut bundle.requests[4] else {
            panic!("the corpus's request 4 is a TrustWp request");
        };
        let atom = trust_wp
            .provenance
            .replay_context
            .atoms
            .iter_mut()
            .find(|atom| atom.kind == NativeReplayAtomKind::Assumption)
            .expect("the corpus's TrustWp request 4 carries an Assumption atom");
        atom.formula.schema = schema.to_string();
        atom.formula.payload = payload.to_string();
        atom.formula.smtlib = None;
        atom.payload_digest = atom.expected_payload_digest();
    }

    /// LIAR: a replay atom states obligation 0's number inside a formula that
    /// is not its cited obligation's own. That gives the number to another
    /// formula, so it names neither, whichever obligation the atom cites.
    #[test]
    fn a_number_an_atom_states_inside_another_formula_is_ambiguous() {
        let mut bundle = corpus_with_bridge_atom();
        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1}}"#,
        );
        let ids = index(&bundle);
        assert!(ids.is_ambiguous(1));
        assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(2));
        let renderings = row_renderings(&mut bundle);
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &ids),
            AssertionIdCorroboration::None
        );

        // An atom that cites no obligation gives it to no obligation's formula.
        let NativeVerificationRequest::TrustWp(trust_wp) = &mut bundle.requests[4] else {
            panic!("the corpus's request 4 is a TrustWp request");
        };
        for atom in &mut trust_wp.provenance.replay_context.atoms {
            if atom.formula.schema == TRUST_TYPES_FORMULA_SCHEMA_V1 {
                atom.obligation = None;
            }
        }
        assert!(index(&bundle).is_ambiguous(1));
    }

    /// LIAR: a replay atom's formula renders an assertion identity unreadably.
    #[test]
    fn an_unreadable_atom_formula_withdraws_every_number() {
        let mut bundle = corpus_with_bridge_atom();
        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
        );
        let ids = index(&bundle);
        assert!(
            ids.unreadable()
                .is_some_and(|reason| reason.contains("replay atom")),
            "{ids:?}"
        );
        assert!(ids.is_ambiguous(1) && ids.is_ambiguous(0));
    }

    /// CONTROL: an atom whose formula IS its obligation's formula is that
    /// obligation's own rendering, not another one. Obligation 2's formula
    /// renders its own number 0, and every TrustWp atom citing it states that
    /// same formula: 0 stays one obligation's number. The same number inside a
    /// DIFFERENT formula on one of those atoms is ambiguous.
    #[test]
    fn an_atom_restating_its_obligations_formula_is_that_obligation() {
        let own = r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:0","native_assertion_id":0}}"#;
        let mut bundle = corpus_with_bridge_atom();
        let formula = bundle.module.proof_obligations[2]
            .formula
            .as_mut()
            .expect("corpus obligation 2 states a formula");
        formula.schema = TRUST_TYPES_FORMULA_SCHEMA_V1.to_string();
        formula.payload = own.to_string();
        formula.smtlib = None;
        let restated = formula.clone();
        let NativeVerificationRequest::TrustWp(trust_wp) = &mut bundle.requests[4] else {
            panic!("the corpus's request 4 is a TrustWp request");
        };
        for atom in &mut trust_wp.provenance.replay_context.atoms {
            atom.formula = restated.clone();
            atom.payload_digest = atom.expected_payload_digest();
        }
        validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
            .expect("obligation 2's renderings agree");
        let ids = index(&bundle);
        assert_eq!(ids.unreadable(), None);
        assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(1));

        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":false},"source":{"native_assertion_id":0}}"#,
        );
        assert!(index(&bundle).is_ambiguous(0));
    }

    /// Only the CITING request can license. The corpus's TrustWp request 4
    /// carries an `Assertion` atom for obligation 2 stating its number 0; a row
    /// for obligation 2 cited by the TrustVc request reads that request's
    /// context, which has no atom for it, so nothing is licensed.
    #[test]
    fn an_atom_of_another_request_licenses_nothing() {
        let mut bundle = corpus_with_bridge_atom();
        let obligation = bundle.module.proof_obligations[2].clone();
        let source = bundle
            .compiler_facts
            .obligation_source(obligation.id)
            .cloned();
        let NativeVerificationRequest::TrustWp(trust_wp) = &bundle.requests[4] else {
            panic!("the corpus's request 4 is a TrustWp request");
        };
        let elsewhere = AssertionIdRenderings::cited_by(
            &obligation,
            source.as_ref(),
            &trust_wp.provenance.replay_context,
        );
        assert_eq!(
            elsewhere.request_atoms,
            Some(vec![Some(0)]),
            "the atom exists, in another request"
        );
        let renderings = AssertionIdRenderings::cited_by(
            &obligation,
            source.as_ref(),
            trust_vc_context(&mut bundle),
        );
        assert_eq!(renderings.request_atoms, Some(Vec::new()));
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &AssertionIdIndex::default()),
            AssertionIdCorroboration::None
        );
    }

    /// Predicate documents (`trust-types.Formula@1`) that are JSON but not an
    /// object: the round-16 review's shapes, each rendering obligation 0's
    /// number 1 or nothing readable at all.
    const NON_OBJECT_DOCUMENTS: &[(&str, &str)] = &[
        (
            r#"[{"formula":{"Bool":true},"source":{"native_assertion_id":1}}]"#,
            "the source record wrapped in an array",
        ),
        (
            r#""{\"formula\":{\"Bool\":true},\"source\":{\"native_assertion_id\":1}}""#,
            "the record as a JSON string",
        ),
        ("1", "the bare number 1"),
        ("true", "a boolean"),
        ("null", "null"),
        ("[]", "an empty array"),
    ];

    /// LIAR (round 16): under the nested schema a document that is not an
    /// object cannot say whether it carries a source record, so it is
    /// UNREADABLE, never `Absent`. `Value::get("source")` answers `None` for all
    /// of these, which read as "no source block". Beside an A it refuses the
    /// bundle, as the top-level schema's non-object document always did.
    #[test]
    fn a_predicate_document_that_is_not_an_object_is_unreadable() {
        for (payload, label) in NON_OBJECT_DOCUMENTS {
            let obligation = obligation(Some("rust-assertion:7"), Some(payload));
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::DocumentNotAnObject,
                "{label}"
            );
            assert_eq!(renderings.payload_native, None, "{label}");
            assert!(
                renderings
                    .payload_unreadable
                    .as_deref()
                    .is_some_and(|reason| reason.contains("not a JSON object")),
                "{label}: {renderings:?}"
            );
            assert!(
                renderings
                    .describe()
                    .contains("predicate payload document is not an object"),
                "{label}: the state must be NAMED: {}",
                renderings.describe()
            );
            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(compiler_source(Some(7)));
            validate_assertion_id_renderings(&module, &facts)
                .expect_err("an unreadable document beside an A must refuse the bundle");
        }
    }

    /// Identity keys stated outside the record the schema reads: the round-16
    /// review's three wrong-schema shapes, and the same key in the other places
    /// a document can hide one.
    const STRAY_IDENTITY_KEYS: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"native_assertion_id":1,"assertion_id":"rust-assertion:7"}"#,
            "the top-level record under the nested schema",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"native_assertion_id":"1"}"#,
            "an unreadable C beside the predicate, under the nested schema",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"source":{"native_assertion_id":1},"assertion_id":"rust-assertion:7"}"#,
            "a nested record under the top-level schema",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7},"native_assertion_id":1}"#,
            "a second C beside a readable record",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"And":[{"Bool":true},{"native_assertion_id":1}]},"source":{"native_assertion_id":7}}"#,
            "a C inside the predicate",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"span":{"native_assertion_id":1}}}"#,
            "a C inside the record's span",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"span":{"file":0,"assertion_id":"rust-assertion:1"}}"#,
            "a D inside the top-level record's span",
        ),
    ];

    /// LIAR (round 16): a payload that states an identity key outside the
    /// record its schema reads has no single reading. It is unreadable, and
    /// beside an A it refuses the bundle.
    #[test]
    fn an_identity_key_outside_the_source_record_is_unreadable() {
        for (schema, payload, label) in STRAY_IDENTITY_KEYS {
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::StrayIdentityKey,
                "{label}"
            );
            assert_eq!(renderings.payload_native, None, "{label}");
            assert_eq!(renderings.payload_source, None, "{label}");
            assert!(
                renderings
                    .payload_unreadable
                    .as_deref()
                    .is_some_and(|reason| reason.contains("outside the source record")),
                "{label}: {renderings:?}"
            );
            assert!(
                renderings
                    .describe()
                    .contains("payload states an identity key outside its source record"),
                "{label}: the state must be NAMED: {}",
                renderings.describe()
            );
            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(compiler_source(Some(7)));
            validate_assertion_id_renderings(&module, &facts)
                .expect_err("a stray identity key beside an A must refuse the bundle");
        }
    }

    /// CONTROL for the two liars above: the producer's own shapes stay
    /// readable. `trust-ir-bridge` writes the record with a `span` object under
    /// both schemas, and adds `predicate_parse_failed` / `attempted_predicate`
    /// strings to the top-level one; a string VALUE that spells an identity key
    /// is not a key.
    #[test]
    fn the_producers_own_payload_shapes_stay_readable() {
        let nested = r#"{"formula":{"Ge":[{"Var":["_0","Int"]},{"Int":1}]},"source":{"source_id":"rust:probe/clamp.rs::clamp","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":4,"col_start":5,"line_end":4,"col_end":30}}}"#;
        let top_level = r#"{"source_id":"rust:probe/clamp.rs::clamp","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":4,"col_start":5,"line_end":4,"col_end":30},"predicate_parse_failed":"unparseable-contract-predicate","attempted_predicate":"native_assertion_id == assertion_id"}"#;
        for (schema, payload, block) in [
            (
                TRUST_TYPES_FORMULA_SCHEMA_V1,
                nested,
                PayloadSourceBlock::Object,
            ),
            (
                TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
                top_level,
                PayloadSourceBlock::TopLevelObject,
            ),
        ] {
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(renderings.payload_source_block, block, "{schema}");
            assert_eq!(renderings.payload_unreadable, None, "{schema}");
            assert_eq!(renderings.payload_native, Some(7), "{schema}");
            assert_eq!(
                renderings.payload_source.as_deref(),
                Some("rust-assertion:7"),
                "{schema}"
            );
        }
        // A predicate document with no record and no identity key anywhere is
        // still the stated absence, and a string VALUE inside the predicate
        // that spells an identity key is not a key. (Round 16 made this point
        // with a `note` key beside the predicate; the strict reader refuses
        // that key whatever it holds, so it is a liar now, in
        // `STRICT_SHAPE_LIARS`.)
        let obligation = obligation(
            Some("rust-assertion:7"),
            Some(r#"{"formula":{"Var":["native_assertion_id","Bool"]}}"#),
        );
        let renderings = AssertionIdRenderings::of(&obligation, None);
        assert_eq!(renderings.payload_source_block, PayloadSourceBlock::Absent);
        assert_eq!(renderings.payload_unreadable, None);
    }

    /// LIAR (round 16): the round-14 carrier (obligation 7, no compiler fact,
    /// requested by nobody) with a document that is not an object, or a stray
    /// identity key, withdraws every number.
    #[test]
    fn a_non_object_document_or_a_stray_key_withdraws_every_number() {
        let carriers = NON_OBJECT_DOCUMENTS
            .iter()
            .map(|(payload, label)| (TRUST_TYPES_FORMULA_SCHEMA_V1, *payload, *label))
            .chain(STRAY_IDENTITY_KEYS.iter().copied());
        for (schema, payload, label) in carriers {
            let mut bundle = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut bundle, schema, payload);
            validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
                .unwrap_or_else(|error| panic!("{label}: no A, so no bundle refusal: {error}"));
            let ids = index(&bundle);
            assert!(
                ids.unreadable()
                    .is_some_and(|reason| reason.contains("obligation 7")),
                "{label}: {ids:?}"
            );
            for number in [0, 1, 2, 7, u32::MAX] {
                assert!(ids.is_ambiguous(number), "{label}: {number}");
            }
            let renderings = row_renderings(&mut bundle);
            assert_eq!(
                AssertionIdCorroboration::of(&renderings, &ids),
                AssertionIdCorroboration::None,
                "{label}"
            );
        }
    }

    /// LIAR (round 16): an UNNUMBERED obligation that shares a numbered one's
    /// string carries its number. Obligation 7 (`rust-assertion:7`, no number
    /// anywhere) and obligation 0 relabeled to `rust-assertion:7` / 7: before,
    /// 7 had one carrier and obligation 0 was licensed 7.
    #[test]
    fn an_unnumbered_obligation_sharing_a_string_carries_its_number() {
        let mut bundle = corpus_with_bridge_atom();
        add_unrequested_factless_obligation(&mut bundle, "smtlib2", "(and (i32 lhs) (i32 rhs))");
        relabel(&mut bundle, &[0], "rust-assertion:7", 7);
        validate_assertion_id_renderings(&bundle.module, &bundle.compiler_facts)
            .expect("every numbered rendering agrees");
        gate(&bundle).expect("the atom agrees with its fact");
        let ids = index(&bundle);
        assert_eq!(ids.unreadable(), None);
        assert!(ids.is_ambiguous(7));
        assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(2));
        let renderings = row_renderings(&mut bundle);
        assert_eq!(renderings.compiler_fact, Some(7));
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &ids),
            AssertionIdCorroboration::None
        );

        // THE RESIDUAL, as the control: the same move to a FRESH string. No
        // other obligation names `rust-assertion:9`, so 7 has one carrier and
        // is licensed (the documented move residual).
        let mut moved = corpus_with_bridge_atom();
        add_unrequested_factless_obligation(&mut moved, "smtlib2", "(and (i32 lhs) (i32 rhs))");
        relabel(&mut moved, &[0], "rust-assertion:9", 7);
        let ids = index(&moved);
        assert!(!ids.is_ambiguous(7));
        let renderings = row_renderings(&mut moved);
        assert_eq!(
            AssertionIdCorroboration::of(&renderings, &ids),
            AssertionIdCorroboration::RequestAssertionAtom
        );
    }

    /// LIAR (round 16): a formula no obligation states that renders a numbered
    /// obligation's STRING (D) gives that number to another formula, as a
    /// rendered number (C) does. Obligation 0's string is `rust-assertion:1`.
    #[test]
    fn a_string_a_stray_formula_renders_makes_its_number_ambiguous() {
        let mut bundle = corpus_with_bridge_atom();
        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:1"}}"#,
        );
        let ids = index(&bundle);
        assert_eq!(ids.unreadable(), None);
        assert!(ids.is_ambiguous(1));
        assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(2));

        // CONTROL: a string no obligation carries withdraws nothing.
        let mut bundle = corpus_with_bridge_atom();
        set_trust_wp_assumption_formula(
            &mut bundle,
            r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:5"}}"#,
        );
        let ids = index(&bundle);
        assert!(!ids.is_ambiguous(0) && !ids.is_ambiguous(1) && !ids.is_ambiguous(2));
    }

    /// LIAR (round 16): an atom that states a number beside a formula other
    /// than its cited obligation's own gives the number to that formula. The
    /// round-16 review's shapes: an `Assertion` atom in the TrustWp request, and
    /// an `Assumption` atom in the citing TrustVc request, each citing
    /// obligation 0 with its number 1 and stating obligation 1's formula. The
    /// TrustVc gate compares formulas only for `Assertion` atoms of TrustVc
    /// requests, so neither refuses the bundle.
    #[test]
    fn an_atom_stating_its_number_beside_another_formula_makes_it_ambiguous() {
        let other = |bundle: &NativeVerificationBundle| {
            bundle.module.proof_obligations[1]
                .formula
                .clone()
                .expect("corpus obligation 1 states a formula")
        };
        let own = |bundle: &NativeVerificationBundle| {
            bundle.module.proof_obligations[0]
                .formula
                .clone()
                .expect("corpus obligation 0 states a formula")
        };
        for stated in ["another formula", "its own formula"] {
            let mut trust_wp = corpus_with_bridge_atom();
            let formula = if stated == "another formula" {
                other(&trust_wp)
            } else {
                own(&trust_wp)
            };
            let NativeVerificationRequest::TrustWp(request) = &mut trust_wp.requests[4] else {
                panic!("the corpus's request 4 is a TrustWp request");
            };
            request.obligations.push(ProofId::new(0));
            request.provenance.replay_context.atoms.push(
                NativeReplayAtom::assertion(NativeReplayAtomId::new(99), formula)
                    .with_obligation(ProofId::new(0))
                    .with_assertion_id(NativeAssertionId::new(1)),
            );

            let mut trust_vc = corpus_with_bridge_atom();
            let formula = if stated == "another formula" {
                other(&trust_vc)
            } else {
                own(&trust_vc)
            };
            trust_vc_context(&mut trust_vc).atoms.push(
                NativeReplayAtom::assumption(NativeReplayAtomId::new(99), formula)
                    .with_obligation(ProofId::new(0))
                    .with_assertion_id(NativeAssertionId::new(1)),
            );

            for (label, mut bundle) in [("TrustWp", trust_wp), ("TrustVc", trust_vc)] {
                gate(&bundle).unwrap_or_else(|error| panic!("{label} {stated}: {error}"));
                let ids = index(&bundle);
                let renderings = row_renderings(&mut bundle);
                if stated == "another formula" {
                    assert!(ids.is_ambiguous(1), "{label}");
                    assert_eq!(
                        AssertionIdCorroboration::of(&renderings, &ids),
                        AssertionIdCorroboration::None,
                        "{label}"
                    );
                } else {
                    assert!(!ids.is_ambiguous(1), "{label}: CONTROL");
                    assert_eq!(
                        AssertionIdCorroboration::of(&renderings, &ids),
                        AssertionIdCorroboration::RequestAssertionAtom,
                        "{label}: CONTROL"
                    );
                }
            }
        }
    }

    /// Payload shapes the round-14 to round-16 reviews measured in integration
    /// tests only, and the non-object `source` and top-level documents of the
    /// earlier unit tests, gathered so the table below holds every shape the
    /// reviews produced.
    const FURTHER_REVIEWED_SHAPES: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1e0}}"#,
            "C as 1e0",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":-0}}"#,
            "C as -0",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":[1]}}"#,
            "C as [1]",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":null}}"#,
            "C as null",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":{"0":1}}}"#,
            "C as an object",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"assertion_id":null}}"#,
            "D as null",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":5}"#,
            "a source that is a number",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":[{"native_assertion_id":1}]}"#,
            "a source that is an array wrapping the record",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":null}"#,
            "a source that is null",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            "5",
            "a top-level document that is a number",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            "[]",
            "a top-level document that is an array",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            "null",
            "a top-level document that is null",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"[{"native_assertion_id":1,"assertion_id":"rust-assertion:7"}]"#,
            "a top-level record wrapped in an array",
        ),
    ];

    /// ROUND 17: shapes only the STRICT reader refuses. Each is an object in
    /// the right place that the round-16 reader read as a record, or as a
    /// stated absence, while it hides obligation 0's number 1 (or a string or
    /// a key another reader might take for an identity): a key the shape does
    /// not have, at a level it defines, or a value of the wrong type.
    const STRICT_SHAPE_LIARS: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"note":"native_assertion_id"}"#,
            "a note beside the predicate (round 16's absence control)",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7},"assertion":"rust-assertion:1"}"#,
            "an unknown key beside the record",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"nativeAssertionId":1}}"#,
            "C under a camel-case key",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id ":1}}"#,
            "C under a key with a trailing space",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"Native_Assertion_Id":1}}"#,
            "C under a capitalised key",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native-assertion-id":1}}"#,
            "C under a hyphenated key",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"native_assertion_ids":[1]}}"#,
            "a plural C key beside a readable one",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"source_id":1}}"#,
            "source_id as a number",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"source_id":null}}"#,
            "source_id as null",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"span":"rust-assertion:1"}}"#,
            "a span that is a string",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"span":{"file":0,"line_start":"1"}}}"#,
            "a span line as a string",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"span":{"file":0,"id":1}}}"#,
            "an unknown key in the span",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"span":{"file":{"n":1}}}}"#,
            "a span file that is an object",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"predicate_parse_failed":"x"}}"#,
            "a top-level marker inside a predicate document's record",
        ),
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Bool":true},"Source":{"native_assertion_id":1}}"#,
            "the record under a capitalised key",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"source":{}}"#,
            "an empty `source` wrapper beside a top-level record",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"formula":{"Bool":true}}"#,
            "a predicate under the top-level schema",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"predicate_parse_failed":1}"#,
            "a marker that is not a string",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"nativeAssertionId":1}"#,
            "a camel-case C beside a readable one",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"native_assertion_id":7,"span":[1]}"#,
            "a span that is an array",
        ),
    ];

    /// Every payload shape the reviews produced (rounds 14 to 16) and every
    /// shape only the strict reader refuses (round 17). Each one must be
    /// unreadable.
    fn every_reviewed_shape() -> impl Iterator<Item = (&'static str, &'static str, &'static str)> {
        UNREADABLE_CARRIERS
            .iter()
            .copied()
            .chain(REPEATED_KEY_PAYLOADS.iter().copied())
            .chain(
                NON_OBJECT_DOCUMENTS
                    .iter()
                    .map(|(payload, label)| (TRUST_TYPES_FORMULA_SCHEMA_V1, *payload, *label)),
            )
            .chain(STRAY_IDENTITY_KEYS.iter().copied())
            .chain(FURTHER_REVIEWED_SHAPES.iter().copied())
            .chain(STRICT_SHAPE_LIARS.iter().copied())
    }

    /// THE ONE ACCEPTED SHAPE per schema, byte for byte what `trust-ir-bridge`
    /// writes (`source_json` nested under `source`, or as the whole payload
    /// with the producer's fail-closed markers), rendering C = 7 and D =
    /// `rust-assertion:7`.
    const CANONICAL_SHAPES: &[(&str, &str, &str)] = &[
        (
            TRUST_TYPES_FORMULA_SCHEMA_V1,
            r#"{"formula":{"Ge":[{"Var":["_0","Int"]},{"Int":1}]},"source":{"source_id":"rust:probe/clamp.rs::clamp","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":"probe/clamp.rs","line_start":4,"col_start":5,"line_end":4,"col_end":30}}}"#,
            "the predicate document",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"source_id":"mir-assertions:probe::clamp:panic-freedom","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":"probe/clamp.rs","line_start":4,"col_start":5,"line_end":4,"col_end":30}}"#,
            "the source record",
        ),
        (
            TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
            r#"{"source_id":"rust:probe/clamp.rs::clamp","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":4,"col_start":5,"line_end":4,"col_end":30},"predicate_parse_failed":"unparseable-contract-predicate","attempted_predicate":"native_assertion_id == 1","safety_formula_not_reconstructed":"outside the faithful envelope"}"#,
            "the source record with the producer's three markers",
        ),
    ];

    /// ROUND 17, THE STRICT READER, TABLE-DRIVEN. Every payload shape the
    /// reviews produced is unreadable, and the producer's canonical shape is
    /// the ONLY accepted control. Each liar is fed to the reader, beside a
    /// compiler fact (the bundle is refused), and in two carriers that do not
    /// refuse the bundle: the round-14 unrequested obligation with no compiler
    /// fact, and a replay atom's formula. In each it withdraws every number.
    /// The canonical shape reads C and D in each place and withdraws only its
    /// own number. (The integration test
    /// `every_reviewed_payload_shape_publishes_no_id_in_every_carrier` runs the
    /// same shapes end to end through every carrier, summary clauses and spec
    /// formulas included; they are not built here because naming a
    /// `FunctionSummary` in this file would move the producer-field census.)
    #[test]
    fn only_the_canonical_payload_shape_is_readable() {
        let mut liars = 0;
        for (schema, payload, label) in every_reviewed_shape() {
            liars += 1;
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert!(
                renderings.payload_unreadable.is_some(),
                "{label}: {payload} must be unreadable: {renderings:?}"
            );
            assert!(
                !matches!(
                    renderings.payload_source_block,
                    PayloadSourceBlock::NotDecoded
                        | PayloadSourceBlock::Absent
                        | PayloadSourceBlock::Object
                        | PayloadSourceBlock::TopLevelObject
                ),
                "{label}: an unreadable payload names an unreadable state: {renderings:?}"
            );
            assert_eq!(renderings.payload_native, None, "{label}");
            assert_eq!(renderings.payload_source, None, "{label}");

            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(compiler_source(Some(7)));
            validate_assertion_id_renderings(&module, &facts)
                .expect_err(&format!("{label}: beside an A the bundle must be refused"));

            let mut factless = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut factless, schema, payload);
            validate_assertion_id_renderings(&factless.module, &factless.compiler_facts)
                .unwrap_or_else(|error| panic!("{label}: no A, so no bundle refusal: {error}"));
            let mut atom = corpus_with_bridge_atom();
            set_trust_wp_assumption_formula_under(&mut atom, schema, payload);
            for (carrier, mut bundle) in [
                ("an unrequested obligation", factless),
                ("a replay atom's formula", atom),
            ] {
                let ids = index(&bundle);
                assert!(ids.unreadable().is_some(), "{carrier}: {label}: {ids:?}");
                for number in [0, 1, 2, 7, u32::MAX] {
                    assert!(ids.is_ambiguous(number), "{carrier}: {label}: {number}");
                }
                let renderings = row_renderings(&mut bundle);
                assert_eq!(
                    AssertionIdCorroboration::of(&renderings, &ids),
                    AssertionIdCorroboration::None,
                    "{carrier}: {label}"
                );
            }
        }
        assert_eq!(
            liars,
            UNREADABLE_CARRIERS.len()
                + REPEATED_KEY_PAYLOADS.len()
                + NON_OBJECT_DOCUMENTS.len()
                + STRAY_IDENTITY_KEYS.len()
                + FURTHER_REVIEWED_SHAPES.len()
                + STRICT_SHAPE_LIARS.len()
        );

        for (schema, payload, label) in CANONICAL_SHAPES {
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(renderings.payload_unreadable, None, "{label}");
            assert_eq!(
                renderings.payload_source_block,
                if *schema == TRUST_TYPES_FORMULA_SCHEMA_V1 {
                    PayloadSourceBlock::Object
                } else {
                    PayloadSourceBlock::TopLevelObject
                },
                "{label}"
            );
            assert_eq!(renderings.payload_native, Some(7), "{label}");
            assert_eq!(
                renderings.payload_source.as_deref(),
                Some("rust-assertion:7"),
                "{label}"
            );

            let mut module = Module::new("probe");
            module.proof_obligations.push(obligation);
            let mut facts = NativeCompilerFacts::default();
            facts.obligation_sources.push(compiler_source(Some(7)));
            validate_assertion_id_renderings(&module, &facts)
                .unwrap_or_else(|error| panic!("{label}: it agrees with its A: {error}"));

            let mut factless = corpus_with_bridge_atom();
            add_unrequested_factless_obligation(&mut factless, schema, payload);
            let mut atom = corpus_with_bridge_atom();
            set_trust_wp_assumption_formula_under(&mut atom, schema, payload);
            for (carrier, mut bundle) in [
                ("an unrequested obligation", factless),
                ("a replay atom's formula", atom),
            ] {
                let ids = index(&bundle);
                assert_eq!(ids.unreadable(), None, "{carrier}: {label}");
                assert!(
                    !ids.is_ambiguous(0) && !ids.is_ambiguous(1) && !ids.is_ambiguous(2),
                    "{carrier}: {label}: {ids:?}"
                );
                let renderings = row_renderings(&mut bundle);
                assert_eq!(
                    AssertionIdCorroboration::of(&renderings, &ids).licensed(&renderings),
                    Some(1),
                    "{carrier}: {label}"
                );
            }
        }
    }

    /// The strict reader names the rule a payload broke, and the key or value
    /// that broke it, so a refusal says where to look.
    #[test]
    fn a_payload_that_is_not_the_canonical_shape_says_where() {
        for (schema, payload, needle) in [
            (
                TRUST_TYPES_FORMULA_SCHEMA_V1,
                r#"{"formula":{"Bool":true},"note":"x"}"#,
                "`$.note`",
            ),
            (
                TRUST_TYPES_FORMULA_SCHEMA_V1,
                r#"{"formula":{"Bool":true},"source":{"nativeAssertionId":1}}"#,
                "`$.source.nativeAssertionId`",
            ),
            (
                TRUST_TYPES_FORMULA_SCHEMA_V1,
                r#"{"formula":{"Bool":true},"source":{"span":{"file":0,"id":1}}}"#,
                "`$.source.span.id`",
            ),
            (
                TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
                r#"{"native_assertion_id":7,"source":{}}"#,
                "`$.source`",
            ),
            (
                TRUST_IR_OBLIGATION_SOURCE_SCHEMA_V1,
                r#"{"native_assertion_id":7,"predicate_parse_failed":1}"#,
                "`$.predicate_parse_failed` is 1",
            ),
            (
                TRUST_TYPES_FORMULA_SCHEMA_V1,
                r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
                "which is not a u32",
            ),
        ] {
            let mut obligation = obligation(Some("rust-assertion:7"), Some(payload));
            obligation.formula.as_mut().expect("formula").schema = schema.to_string();
            let renderings = AssertionIdRenderings::of(&obligation, None);
            assert_eq!(
                renderings.payload_source_block,
                PayloadSourceBlock::NotCanonical,
                "{payload}"
            );
            let reason = renderings.payload_unreadable.as_deref().unwrap_or_default();
            assert!(
                reason.contains("not the one shape that schema accepts") && reason.contains(needle),
                "{payload}: {reason}"
            );
            assert!(
                renderings
                    .describe()
                    .contains("payload is not the one shape its schema accepts"),
                "{payload}: the state must be NAMED: {}",
                renderings.describe()
            );
        }
    }
}
