// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests of the coverage rules, over [`judge_certificate`] and the rule-5
//! formula reading, without forging a report.

use super::*;
use trust_ir::{ObligationKind, ProofDigest, ProofStatus};
use TrustVcNativeTrustIrCertificateRejection as Rejection;

fn reference(obligation: u32, prover: &str) -> ProofCertificateRef {
    ProofCertificateRef {
        obligation: ProofId::new(obligation),
        prover: prover.to_string(),
        evidence_digest: ProofDigest::sha256([obligation as u8 + 1; 32]),
    }
}

fn established(bound: CoverageBound, certificate: &ProofCertificateRef) -> CertificateCoverage {
    CertificateCoverage::Established {
        bound,
        basis: CoverageBasis::KernelReplayedClaim {
            certificate: certificate.clone(),
            family: KernelClaimFamily::ContractGroundDecision,
        },
    }
}

fn refusal() -> ValidationError {
    ValidationError::CoverageRowExceedsEstablished {
        obligation: 3,
        recorded: "Unbounded".to_string(),
        established: "nothing established".to_string(),
    }
}

#[test]
fn only_an_unbounded_kernel_basis_naming_this_certificate_establishes() {
    let this = reference(0, "trust_vc");
    let judgement = judge_certificate(
        &this,
        true,
        None,
        established(CoverageBound::Unbounded, &this),
        &[],
    );
    assert_eq!(
        judgement,
        CoverageJudgement {
            basis: Some(TrustVcNativeCoverageBasis::KernelReplayedClaim {
                obligation_id: 0,
                prover: "trust_vc".to_string(),
                evidence_digest: this.evidence_digest.to_string(),
                family: TrustVcNativeKernelClaimFamily::ContractGroundDecision,
            }),
            rejections: Vec::new(),
            detail: None,
        }
    );
}

/// Rule 3's certificate-equality check. Upstream keys verdicts by
/// certificate, so a borrowed basis cannot come out of a real report;
/// the check stays load-bearing if that ever changes.
#[test]
fn a_basis_naming_another_certificate_does_not_establish() {
    let this = reference(0, "trust_vc");
    let sibling = reference(0, "z3");
    let judgement = judge_certificate(
        &this,
        true,
        None,
        established(CoverageBound::Unbounded, &sibling),
        &[],
    );
    assert_eq!(judgement.basis, None);
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageBasisNotThisCertificate]
    );
}

#[test]
fn an_established_bound_short_of_unbounded_is_not_release_grade() {
    let this = reference(0, "trust_vc");
    for bound in [
        CoverageBound::UnwindBounded { depth: 1 },
        CoverageBound::ModelBounded { size: 4 },
        CoverageBound::Unrecorded,
    ] {
        let judgement = judge_certificate(&this, true, None, established(bound, &this), &[]);
        assert_eq!(judgement.basis, None, "{bound:?}");
        assert_eq!(
            judgement.rejections,
            [Rejection::CertificateCoverageBounded],
            "{bound:?}"
        );
    }
}

#[test]
fn an_unchecked_report_establishes_nothing() {
    let this = reference(0, "trust_vc");
    let judgement = judge_certificate(
        &this,
        false,
        None,
        established(CoverageBound::Unbounded, &this),
        &[],
    );
    assert_eq!(judgement.basis, None);
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageUndetermined]
    );
}

#[test]
fn a_refusal_anywhere_rejects_an_established_certificate() {
    let this = reference(0, "trust_vc");
    let judgement = judge_certificate(
        &this,
        true,
        None,
        established(CoverageBound::Unbounded, &this),
        &[refusal()],
    );
    assert_eq!(judgement.basis, None);
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageRefused]
    );
    assert_eq!(judgement.detail, Some(refusal().to_string()));
}

#[test]
fn undetermined_and_refused_verdicts_are_named() {
    let this = reference(0, "trust_vc");
    for (reason, expected) in [
        (
            CoverageUndeterminedReason::NotTheReplayedCertificate,
            Rejection::CertificateCoverageBasisNotThisCertificate,
        ),
        (
            CoverageUndeterminedReason::NoBasis,
            Rejection::CertificateCoverageUndetermined,
        ),
        (
            CoverageUndeterminedReason::ClaimFamilyUnclassified,
            Rejection::CertificateCoverageUndetermined,
        ),
        (
            CoverageUndeterminedReason::KernelUnavailable,
            Rejection::CertificateCoverageUndetermined,
        ),
    ] {
        let judgement = judge_certificate(
            &this,
            true,
            None,
            CertificateCoverage::Undetermined {
                reason: reason.clone(),
            },
            &[],
        );
        assert_eq!(judgement.basis, None, "{reason:?}");
        assert_eq!(judgement.rejections, [expected], "{reason:?}");
    }
    let judgement = judge_certificate(
        &this,
        true,
        None,
        CertificateCoverage::Refused(refusal()),
        &[],
    );
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageRefused]
    );
}

fn formula(schema: &str, payload: &str, smtlib: Option<&str>, sort: Option<&str>) -> ProofFormula {
    let mut formula = ProofFormula::new(schema, payload);
    formula.smtlib = smtlib.map(str::to_string);
    formula.sort = sort.map(str::to_string);
    formula
}

fn obligation(id: u32, formula: Option<ProofFormula>) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Discharged,
        description: "rule 5".to_string(),
        formula,
        function: None,
        source: None,
        site: None,
        spec: None,
    }
}

/// Rule 5 holds exactly for an `smtlib2` formula whose payload trust-ir's
/// SMT-LIB2 reader reads as one `Bool` term over its own bindings, whose
/// rendering, if any, IS its payload and whose sort, if any, is `Bool`. (A
/// clause over a BOUND name is exercised end to end, with a certificate
/// trust-ir mints for it, in `tests/native_coverage_formula_text.rs`.)
#[test]
fn a_formula_states_one_smtlib_text_only_as_an_agreeing_smtlib2_predicate() {
    for one in [
        formula("smtlib2", "(>= 5 0)", Some("(>= 5 0)"), Some("Bool")),
        formula("smtlib2", "(>= 5 0)", None, None),
        ProofFormula::smtlib2("(>= 5 0)", "Bool"),
        formula("smtlib2", "(>=\t5\r\n0)", None, None),
    ] {
        assert_eq!(formula_text_defect(Some(&one)), None, "{one:?}");
    }
    for (label, defective, words) in [
        (
            "payload and rendering disagree",
            formula("smtlib2", "(>= 0 5)", Some("(>= 5 0)"), Some("Bool")),
            "two different",
        ),
        (
            "rendering differs by whitespace only",
            formula("smtlib2", "(>= 5 0)", Some("(>=  5 0)"), None),
            "two different",
        ),
        (
            "opaque payload, no rendering",
            formula("trust-types.Formula@1", "(>= 5 0)", None, None),
            "opaque",
        ),
        (
            "opaque payload with a rendering",
            formula(
                "trust-types.Formula@1",
                "{}",
                Some("(>= 5 0)"),
                Some("Bool"),
            ),
            "opaque",
        ),
        (
            "schema differs by case",
            formula("SMTLIB2", "(>= 5 0)", Some("(>= 5 0)"), None),
            "opaque",
        ),
        (
            "payload spaced with U+3000",
            formula("smtlib2", "(>=\u{3000}5\u{3000}0)", None, None),
            "neither printable ASCII",
        ),
        (
            "payload spaced with VT and FF, rendering equal",
            formula(
                "smtlib2",
                "(>=\u{0B}5\u{0C}0)",
                Some("(>=\u{0B}5\u{0C}0)"),
                None,
            ),
            "neither printable ASCII",
        ),
        (
            "payload naming a primed symbol",
            formula("smtlib2", "(>= x' 0)", Some("(>= x' 0)"), None),
            "not SMT-LIB source trust-ir reads",
        ),
        (
            "payload with a leading-zero numeral",
            formula("smtlib2", "(>= 007 3)", None, None),
            "not SMT-LIB source trust-ir reads",
        ),
        (
            "payload naming a symbol it does not bind",
            formula("smtlib2", "(>= x 0)", None, None),
            "undeclared variable `x`",
        ),
        (
            "not a predicate",
            formula("smtlib2", "(>= 5 0)", Some("(>= 5 0)"), Some("Int")),
            "sort `Int`",
        ),
        (
            "a bit-vector sort",
            formula("smtlib2", "(>= 5 0)", None, Some("(_ BitVec 8)")),
            "sort `(_ BitVec 8)`",
        ),
        (
            "`Bool` spelled in lower case",
            formula("smtlib2", "(>= 5 0)", None, Some("bool")),
            "sort `bool`",
        ),
        (
            "a lone conjunction",
            formula("smtlib2", "(and (>= 5 0))", None, None),
            "not SMT-LIB source trust-ir reads",
        ),
        (
            "a lone disjunction, rendering equal",
            formula(
                "smtlib2",
                "(or (>= 5 0))",
                Some("(or (>= 5 0))"),
                Some("Bool"),
            ),
            "not SMT-LIB source trust-ir reads",
        ),
    ] {
        let defect = formula_text_defect(Some(&defective))
            .unwrap_or_else(|| panic!("{label}: {defective:?} states one text"));
        assert!(defect.contains(words), "{label}: {defect}");
    }
    assert!(formula_text_defect(None).is_some_and(|defect| defect.contains("no formula")));
}

/// Per obligation id; an id stated twice is a defect even when both of
/// its formulas are fine.
#[test]
fn formula_defects_are_keyed_by_obligation_and_a_twice_stated_id_is_one() {
    let good = || Some(ProofFormula::smtlib2("(>= 5 0)", "Bool"));
    let defects = formula_defects(&[
        obligation(0, good()),
        obligation(
            1,
            Some(formula("smtlib2", "(>= 0 5)", Some("(>= 5 0)"), None)),
        ),
        obligation(2, good()),
        obligation(2, good()),
    ]);
    assert_eq!(defects.get(&ProofId::new(0)), Some(&None));
    assert!(matches!(defects.get(&ProofId::new(1)), Some(Some(_))));
    assert!(
        defects
            .get(&ProofId::new(2))
            .is_some_and(|defect| defect.as_deref().is_some_and(|d| d.contains("twice"))),
        "{defects:?}"
    );
    assert_eq!(defects.get(&ProofId::new(3)), None);
}

/// Rule 5 turns an established certificate UNDETERMINED, and never masks
/// a refusal (rule 4) or an unchecked report (rule 2).
#[test]
fn a_formula_defect_blocks_establishment_and_masks_no_refusal() {
    let this = reference(0, "trust_vc");
    let defect = Some("the obligation states no formula");
    let judgement = judge_certificate(
        &this,
        true,
        defect,
        established(CoverageBound::Unbounded, &this),
        &[],
    );
    assert_eq!(judgement.basis, None);
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageUndetermined]
    );
    assert!(judgement
        .detail
        .is_some_and(|detail| detail.starts_with("the obligation states no formula; ")));

    let judgement = judge_certificate(
        &this,
        true,
        defect,
        established(CoverageBound::Unbounded, &this),
        &[refusal()],
    );
    assert_eq!(
        judgement.rejections,
        [Rejection::CertificateCoverageRefused]
    );
    let judgement = judge_certificate(
        &this,
        false,
        defect,
        established(CoverageBound::Unbounded, &this),
        &[],
    );
    assert_eq!(
        judgement.detail.as_deref(),
        Some("coverage establishment report is UNCHECKED: the bundle did not validate for it")
    );
}
