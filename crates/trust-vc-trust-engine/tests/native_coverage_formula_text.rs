// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Coverage rule 5 (`native_coverage`): a kernel-replayed certificate is
//! admitted only for an obligation that states exactly ONE SMT-LIB formula
//! text — schema `smtlib2` with a payload trust-ir's SMT-LIB2 reader reads
//! as one `Bool` term over the clause's own bindings, no `smtlib` rendering
//! or one equal to the payload, no sort but `Bool`.
//!
//! Every case below re-binds the corpus's CleanCic certificate
//! (`Eq.refl true`) to an edited obligation with trust-ir's own lineage
//! digest, and rewrites its request's `Assertion` replay atom to the edited
//! formula, so the kernel replays it against that obligation whenever trust-ir
//! grounds the formula at all and the atom never disagrees with it. Each case
//! was ADMITTED (`certificates_admitted`, no rejection reason) on the tree
//! before rule 5.
//!
//! Upstream grounds only `ProofFormula::smtlib_text`, read through its one
//! SMT-LIB2 reader: an opaque schema, an `smtlib2` payload beside a different
//! rendering, a payload that is not SMT-LIB source, a formula declared of a
//! sort other than `Bool`, a clause over a theory function symbol
//! (`(>= and 0)`) and a lone connective (`(and (>= 5 0))`) are never
//! kernel-replayed, so upstream's own bundle validator refuses the whole
//! bundle before rule 5 runs. Rule 5's reading of the same clauses is the
//! second line.

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::inst::Inst;
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::request::{NativeVerificationBundle, NativeVerificationRequest};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::ProofObligation;
use trust_vc_trust_engine::{
    TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrCertificateEvidence,
    TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;
use admission_baseline::{
    edit_replayed_obligation, native_bundle_fixture, reseal_module_identity, sync_assertion_atoms,
};
use admission_edits::assert_id_and_formula_liars_refused;

/// The baseline with obligation 0's formula replaced, and certificate 0
/// re-bound to it.
fn with_formula(
    schema: &str,
    payload: &str,
    smtlib: Option<&str>,
    sort: Option<&str>,
) -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    edit_replayed_obligation(&mut bundle, |obligation: &mut ProofObligation| {
        let formula = obligation
            .formula
            .as_mut()
            .expect("the corpus obligation 0 has a formula");
        formula.schema = schema.to_string();
        formula.payload = payload.to_string();
        formula.smtlib = smtlib.map(str::to_string);
        formula.sort = sort.map(str::to_string);
    });
    bundle
}

fn consume(bundle: &NativeVerificationBundle, label: &str) -> TrustVcNativeTrustIrBundleReport {
    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .unwrap_or_else(|error| panic!("{label}: the bundle is valid upstream: {error}"))
}

fn sole_evidence(
    report: &TrustVcNativeTrustIrBundleReport,
) -> TrustVcNativeTrustIrCertificateEvidence {
    let evidence = report.requests()[0].proof_evidence();
    assert_eq!(evidence.len(), 1, "one imported certificate");
    evidence[0].clone()
}

/// The bundle is REFUSED upstream: consuming and validating it both fail,
/// naming `why`, so none of its certificates reaches rule 5 at all.
fn assert_refused_upstream(bundle: &NativeVerificationBundle, label: &str, why: &str) {
    match TrustVcTrustEngine::new().consume_native_trust_ir_bundle(bundle) {
        Ok(report) => panic!("{label}: consumed, verdict {:?}", report.verdict()),
        Err(error) => assert!(error.to_string().contains(why), "{label}: {error}"),
    }
    assert!(
        TrustVcTrustEngine::new()
            .validate_native_trust_ir_bundle(bundle)
            .is_err(),
        "{label}"
    );
}

/// Upstream's refusal of a TrustVc certificate its validator did not replay.
const NOT_REPLAYED: &str = "rejects TrustVc certificate evidence 0/trust_vc";

/// Control: an obligation stating ONE SMT-LIB text — a true ground decision
/// as the payload, spaced with any of SMT-LIB's four whitespace characters,
/// with an equal rendering or none, sort `Bool` or none — keeps its re-bound
/// certificate ADMITTED, so each refusal below is about the formula, not the
/// re-binding. Each control's liar twins (its atom's id forged, its atom
/// asserting another formula) are refused.
#[test]
fn one_smtlib_text_keeps_the_replayed_certificates_coverage() {
    for (payload, smtlib, sort) in [
        ("(>= 7 3)", Some("(>= 7 3)"), Some("Bool")),
        ("(>= 7 3)", None, Some("Bool")),
        ("(>= 7 3)", None, None),
        ("(>=\t7\r\n3)", None, Some("Bool")),
    ] {
        let bundle = with_formula("smtlib2", payload, smtlib, sort);
        let report = consume(&bundle, "one text");
        let evidence = sole_evidence(&report);
        let admission = evidence.release_admission();
        assert!(
            admission.coverage_established() && admission.is_admissible(),
            "{payload:?}/{smtlib:?}/{sort:?}: {:?}",
            admission.rejection_reasons()
        );
        assert_eq!(
            report.verdict(),
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
            "{payload:?}/{smtlib:?}/{sort:?}"
        );
        assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1);
    }
}

/// A/B. A false admission: the `smtlib2` payload `(>= 0 5)` is FALSE,
/// its `smtlib` "rendering of the same formula" `(>= 5 0)` is true, and the
/// kernel replayed the rendering. Upstream now refuses the bundle, naming
/// the two texts: trust-ir-build's validator, which this crate runs first as
/// its input gate.
#[test]
fn an_smtlib2_payload_beside_a_different_rendering_admits_nothing() {
    let bundle = with_formula("smtlib2", "(>= 0 5)", Some("(>= 5 0)"), Some("Bool"));
    assert_refused_upstream(
        &bundle,
        "false payload, true rendering",
        "states two SMT-LIB texts",
    );
}

/// A/B. An OPAQUE payload (schema `trust-types.Formula@1`) with no rendering
/// was grounded as if it were SMT-LIB. It is no longer replayed, so
/// upstream refuses its certificate.
#[test]
fn an_opaque_payload_is_never_read_as_smtlib() {
    assert_refused_upstream(
        &with_formula("trust-types.Formula@1", "(>= 5 0)", None, Some("Bool")),
        "opaque payload, no rendering",
        NOT_REPLAYED,
    );
}

/// A/B. An opaque payload WITH an `smtlib` rendering: the kernel proved the
/// rendering, though the payload says `0 >= 5`. It is no longer replayed,
/// so upstream refuses its certificate.
#[test]
fn an_opaque_payload_is_not_proved_through_its_rendering() {
    assert_refused_upstream(
        &with_formula(
            "trust-types.Formula@1",
            r#"{"Ge":[{"Int":0},{"Int":5}]}"#,
            Some("(>= 5 0)"),
            Some("Bool"),
        ),
        "opaque payload, true rendering",
        NOT_REPLAYED,
    );
}

/// A/B. A formula whose recorded sort is not `Bool` is no predicate, so no
/// Bool decision the kernel replays is its meaning. Before rule 5: admitted.
/// trust-ir grounds only a `Bool` (or unsorted) formula, so the certificate
/// is never replayed and upstream refuses the bundle; before trust-ir did,
/// rule 5 alone refused it.
#[test]
fn a_formula_of_another_sort_admits_nothing() {
    for sort in ["Int", "(_ BitVec 8)", "bool"] {
        assert_refused_upstream(
            &with_formula("smtlib2", "(>= 5 0)", Some("(>= 5 0)"), Some(sort)),
            &format!("sort {sort}"),
            NOT_REPLAYED,
        );
    }
}

/// A/B. An `smtlib2` payload spaced with characters that are not SMT-LIB
/// whitespace, which no SMT-LIB reader accepts (z3: "unexpected character").
/// trust-ir's contract grounder used to split tokens on `char::is_whitespace`
/// and ground it as `(>= 5 0)`; before rule 5 that was admitted, reasons `[]`.
/// The rendering is absent or equal, so no rendering check can see it. The
/// grounder now reads through trust-ir's SMT-LIB2 reader, so the certificate
/// is never replayed and upstream refuses every case; rule 5's reading
/// through the same reader is the second line.
#[test]
fn a_payload_that_is_not_smtlib_source_admits_nothing() {
    let cases = [
        ("ideographic space", "(>=\u{3000}5\u{3000}0)"),
        ("no-break space", "(>=\u{a0}5\u{a0}0)"),
        ("em space", "(>=\u{2003}5\u{2003}0)"),
        ("vertical tab, form feed", "(>=\u{0B}5\u{0C}0)"),
        ("line and paragraph separators", "(>=\u{2028}5\u{2029}0)"),
        ("next line", "(>=\u{85}5\u{85}0)"),
    ]
    .into_iter()
    .flat_map(|(label, text)| {
        [None, Some(text)].map(|rendering| {
            (
                format!("{label}, rendering {}", rendering.is_some()),
                with_formula("smtlib2", text, rendering, Some("Bool")),
            )
        })
    })
    .collect::<Vec<_>>();
    assert_eq!(cases.len(), 12);
    for (label, bundle) in &cases {
        assert_refused_upstream(bundle, label, NOT_REPLAYED);
    }
}

/// The baseline with function 0 retyped to `u32` and obligation
/// 0 a Postcondition of function 0 stating the nonneg clause `payload`, whose
/// one binding reads `symbol` as that parameter at sort `Int`; certificate 0
/// is REPLACED by the one trust-ir's own minter issues for the edited
/// obligation, re-cited and resealed, so the kernel really replays it.
/// `None` when trust-ir mints nothing for it (its grounder refuses the text).
fn with_nonneg_clause(
    payload: &str,
    rendering: Option<&str>,
    symbol: &str,
) -> Option<NativeVerificationBundle> {
    let mut bundle = native_bundle_fixture();
    // `checked_add` retyped to u32 throughout (signature, entry params, the
    // add), so its parameter is an unsigned place a nonneg clause can bind.
    let module = &mut bundle.module;
    module.func_types[0].params = vec![Ty::U32, Ty::U32];
    module.func_types[0].returns = vec![Ty::U32];
    for (_, ty) in &mut module.functions[0].blocks[0].params {
        *ty = Ty::U32;
    }
    for node in &mut module.functions[0].blocks[0].body {
        if let Inst::BinOp { ty, .. } = &mut node.inst {
            *ty = Ty::U32;
        }
    }
    let previous = bundle.module.proof_certificates[0].lineage_ref();
    let obligation = &mut bundle.module.proof_obligations[0];
    obligation.function = Some(FuncId::new(0));
    let formula = obligation
        .formula
        .as_mut()
        .expect("the corpus obligation 0 has a formula");
    formula.payload = payload.to_string();
    formula.smtlib = rendering.map(str::to_string);
    formula.bindings = vec![(
        symbol.to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::Param { index: 0 },
        },
    )];
    let obligation_id = obligation.id;
    sync_assertion_atoms(&mut bundle, obligation_id);
    let prover = bundle.module.proof_certificates[0].prover.clone();
    bundle.module.proof_certificates[0] = contract_clean_cic_certificate_in(
        &bundle.module,
        &bundle.module.proof_obligations[0],
        prover,
    )?;
    let current = bundle.module.proof_certificates[0].lineage_ref();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    let lineage_certificates = bundle
        .lineage
        .nodes
        .iter_mut()
        .flat_map(|node| node.certificates.iter_mut());
    for certificate in request.certificates.iter_mut().chain(lineage_certificates) {
        if *certificate == previous {
            *certificate = current.clone();
        }
    }
    reseal_module_identity(&mut bundle);
    Some(bundle)
}

/// A/B. Texts trust-ir's SMT-LIB2 reader refuses: `'` is in no SMT-LIB
/// token (z3 answers `(declare-const x' Int)` with "unexpected character"
/// and drops the assertion), and `007` is no SMT-LIB numeral (nor a symbol).
/// trust-ir's contract grounder used to read them anyway, binding `x'` as a
/// name and grounding `007` as 7; before rule 5 the kernel replay
/// established coverage (admitted, reasons `[]`, basis
/// `kernel_replayed_claim`, measured end to end). The grounder now reads
/// through the SMT-LIB2 reader: trust-ir mints no certificate for a clause
/// over a primed name, and a certificate re-bound to a non-numeral is never
/// replayed, so upstream refuses its bundle. The controls — the same clause
/// over a plain name, and a canonical numeral — are admitted, and their liar
/// twins refused.
#[test]
fn a_text_trust_ir_does_not_read_as_smtlib_admits_nothing() {
    let control = with_nonneg_clause("(>= x 0)", None, "x").expect("the control mints");
    let numeral_control = with_formula("smtlib2", "(>= 7 3)", None, Some("Bool"));
    for (label, bundle) in [
        ("nonneg control", &control),
        ("numeral control", &numeral_control),
    ] {
        let evidence = sole_evidence(&consume(bundle, label));
        let admission = evidence.release_admission();
        assert!(
            admission.coverage_established() && admission.is_admissible(),
            "{label}: {:?}",
            admission.rejection_reasons()
        );
        assert_eq!(assert_id_and_formula_liars_refused(bundle), 1, "{label}");
    }
    for (payload, symbol) in [
        ("(>= x' 0)", "x'"),
        ("(<= 0 r'')", "r''"),
        ("(>= a'b 0)", "a'b"),
    ] {
        for rendering in [None, Some(payload)] {
            assert!(
                with_nonneg_clause(payload, rendering, symbol).is_none(),
                "{payload}, rendering {}: trust-ir minted a certificate",
                rendering.is_some()
            );
        }
    }
    for (payload, rendering) in [("(>= 007 3)", None), ("(>= 7 03)", Some("(>= 7 03)"))] {
        assert_refused_upstream(
            &with_formula("smtlib2", payload, rendering, Some("Bool")),
            &format!("{payload}, rendering {}", rendering.is_some()),
            NOT_REPLAYED,
        );
    }
}

/// A/B. Clauses trust-ir's one reader does not read. A nonneg clause over an
/// SMT-LIB2 theory function symbol (`(>= and 0)`: z3 refuses
/// `(declare-const and Int)`, "invalid declaration, builtin symbol") and a
/// lone `and` / `or` (SMT-LIB2 Core declares both `:left-assoc` over two or
/// more arguments). trust-ir mints no certificate for the first and never
/// replays the second, so upstream refuses its bundle; before trust-ir read
/// them through its reader, each was minted or kernel-replayed upstream and
/// only rule 5 refused it. The controls — a clause over a plain name, and a
/// two-argument connective — are admitted.
#[test]
fn a_theory_symbol_or_a_lone_connective_admits_nothing() {
    let nonneg_control = with_nonneg_clause("(>= x 0)", None, "x").expect("the control mints");
    let connective_control = with_formula("smtlib2", "(and (>= 5 0) (>= 7 3))", None, Some("Bool"));
    for (label, bundle) in [
        ("nonneg control", &nonneg_control),
        ("two-argument connective control", &connective_control),
    ] {
        let evidence = sole_evidence(&consume(bundle, label));
        let admission = evidence.release_admission();
        assert!(
            admission.coverage_established() && admission.is_admissible(),
            "{label}: {:?}",
            admission.rejection_reasons()
        );
    }
    let minted: Vec<&str> = [
        "and", "or", "xor", "not", "ite", "distinct", "div", "mod", "abs", "bvadd", "bvnot",
        "concat",
    ]
    .into_iter()
    .filter(|name| {
        let payload = format!("(>= {name} 0)");
        with_nonneg_clause(&payload, None, name).is_some()
            || with_nonneg_clause(&payload, Some(&payload), name).is_some()
    })
    .collect();
    assert!(
        minted.is_empty(),
        "trust-ir minted a certificate over {minted:?}"
    );
    for payload in ["(and (>= 5 0))", "(or (>= 5 0))"] {
        for rendering in [None, Some(payload)] {
            assert_refused_upstream(
                &with_formula("smtlib2", payload, rendering, Some("Bool")),
                &format!("{payload}, rendering {}", rendering.is_some()),
                NOT_REPLAYED,
            );
        }
    }
}
