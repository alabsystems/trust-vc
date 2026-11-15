// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The trust-ir body lane v0: positives, liars, refusals, and the pin that
//! the SERIALIZED discharge path still fails loudly.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, FIXTURE_FUNCTION};
use trust_ir::request::{NativeVerificationBundle, NativeVerificationRequest};
use trust_ir::{
    AssertKind, AssertOverflowOp, Block, BlockId, CallingConv, Constant, FuncTyId, ICmpOp, Inst,
    InstrNode, ObligationKind, ObligationSite, OverflowOp, PanicLocation, PanicSite,
    ProofCertificate, ProofEvidence, ProofId, ProofStatus, Ty, UnOp, ValueId,
};
use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, BodyReading, TrustIrBodyError, TrustIrBodyOptions,
    TrustIrBodyRefusal, TrustIrBodyReport, TrustIrBodyVerdict, TrustProofPolicy,
    TrustVcTrustEngine, HAVOC_INSTANTIATION_NOTE,
};

fn run(fixture: &Fixture) -> TrustIrBodyReport {
    TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions::default(),
        )
        .unwrap_or_else(|error| panic!("{} should reach a report: {error}", fixture.name))
}

fn verdict(report: &TrustIrBodyReport, id: ProofId) -> &TrustIrBodyVerdict {
    &report
        .obligation(id)
        .unwrap_or_else(|| panic!("obligation {id:?} should be reported"))
        .verdict
}

#[track_caller]
fn expect_discharged(fixture: &Fixture, report: &TrustIrBodyReport, id: ProofId) {
    match verdict(report, id) {
        TrustIrBodyVerdict::DischargedAdvisory { .. } => {}
        other => panic!(
            "{} {id:?}: expected DischargedAdvisory, got {other:?}",
            fixture.name
        ),
    }
}

#[track_caller]
fn expect_refuted(fixture: &Fixture, report: &TrustIrBodyReport, id: ProofId) {
    match verdict(report, id) {
        TrustIrBodyVerdict::Refuted { .. } => {}
        other => panic!("{} {id:?}: expected Refuted, got {other:?}", fixture.name),
    }
}

#[track_caller]
fn expect_refusal<'a>(
    fixture: &Fixture,
    report: &'a TrustIrBodyReport,
    id: ProofId,
) -> &'a TrustIrBodyRefusal {
    match verdict(report, id) {
        TrustIrBodyVerdict::NotAnswerable(refusal) => refusal,
        other => panic!(
            "{} {id:?}: expected NotAnswerable, got {other:?}",
            fixture.name
        ),
    }
}

/// No fixture in this suite may ever be discharged by accident.
#[track_caller]
fn expect_never_discharged(fixture: &Fixture, report: &TrustIrBodyReport) {
    for obligation in &report.obligations {
        assert!(
            !obligation.verdict.is_discharged_advisory(),
            "{}: {:?} must not be discharged",
            fixture.name,
            obligation.proof_id
        );
    }
}

// ---------------------------------------------------------------------------
// Positives
// ---------------------------------------------------------------------------

#[test]
fn guarded_checked_add_u8_is_discharged_advisory() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = run(&fixture);
    assert!(
        report.function_refusal.is_none(),
        "{:?}",
        report.function_refusal
    );
    assert_eq!(report.obligations.len(), 1);
    expect_discharged(&fixture, &report, fixture.obligations[0]);

    let TrustIrBodyVerdict::DischargedAdvisory {
        premise_witness, ..
    } = verdict(&report, fixture.obligations[0])
    else {
        unreachable!("checked above");
    };
    // The witness must satisfy the guards it was produced under.
    for (_, scalar) in &premise_witness.params {
        let trust_vc_trust_engine::TrustIrScalar::Int { value, .. } = scalar else {
            panic!("u8 parameters are integers");
        };
        assert!(
            (0..100).contains(value),
            "witness {value} violates the guard"
        );
    }
    // Advisory, with no lowering witness and nothing convertible to a verdict.
    assert_eq!(
        report.schema,
        trust_vc_trust_engine::TRUST_IR_BODY_LANE_SCHEMA
    );
    assert_eq!(
        report.authority,
        trust_vc_trust_engine::TrustIrBodyAuthority::Advisory
    );
    assert_eq!(
        report.lowering_witness,
        trust_vc_trust_engine::LoweringWitness::None
    );
    // The producer's own claims were seen and not used.
    assert!(report.ignored_inputs.formulas);
    assert!(report.ignored_inputs.annotations);
    assert!(report.unobligated_asserts.is_empty());
}

#[test]
fn guarded_checked_add_i8_is_discharged_advisory() {
    let fixture = fixtures::guarded_checked_add_i8();
    let report = run(&fixture);
    expect_discharged(&fixture, &report, fixture.obligations[0]);
}

#[test]
fn both_sites_of_a_three_block_chain_are_discharged() {
    let fixture = fixtures::two_checks_chain();
    let report = run(&fixture);
    assert_eq!(report.obligations.len(), 2);
    for id in &fixture.obligations {
        expect_discharged(&fixture, &report, *id);
    }
}

#[test]
fn wraparound_is_modelled_exactly() {
    let fixture = fixtures::wraparound_semantics();
    let report = run(&fixture);
    // 200 + 100 == 44 at u8.
    expect_discharged(&fixture, &report, fixture.obligations[0]);
    // ... and 44 is not > 200. The earlier assert is not assumed, but it
    // holds for the witness, so this is a plain refutation.
    expect_refuted(&fixture, &report, fixture.obligations[1]);
    assert_eq!(
        report
            .obligation(fixture.obligations[1])
            .unwrap()
            .prior_asserts_not_assumed,
        1
    );
}

#[test]
fn assert_on_a_comparison_result_is_discharged() {
    let fixture = fixtures::expected_true_shape();
    let report = run(&fixture);
    expect_discharged(&fixture, &report, fixture.obligations[0]);
}

#[test]
fn br_parameter_binding_is_order_sensitive() {
    let straight = fixtures::br_param_binding(false);
    let report = run(&straight);
    expect_discharged(&straight, &report, straight.obligations[0]);

    let swapped = fixtures::br_param_binding(true);
    let report = run(&swapped);
    expect_refuted(&swapped, &report, swapped.obligations[0]);
}

// ---------------------------------------------------------------------------
// Liars
// ---------------------------------------------------------------------------

#[test]
fn unguarded_checked_arithmetic_is_refuted_for_every_admitted_op() {
    for (name, op, ty) in [
        ("unguarded_add_u8", OverflowOp::AddOverflow, Ty::U8),
        ("unguarded_sub_u8", OverflowOp::SubOverflow, Ty::U8),
        ("unguarded_mul_u8", OverflowOp::MulOverflow, Ty::U8),
        ("unguarded_add_i8", OverflowOp::AddOverflow, Ty::I8),
        ("unguarded_sub_i8", OverflowOp::SubOverflow, Ty::I8),
        ("unguarded_mul_i8", OverflowOp::MulOverflow, Ty::I8),
    ] {
        let fixture = fixtures::unguarded_checked_op(name, op, ty);
        let report = run(&fixture);
        expect_refuted(&fixture, &report, fixture.obligations[0]);
    }
}

#[test]
fn producer_claims_never_discharge_a_false_obligation() {
    let fixture = fixtures::unguarded_with_producer_claims();
    let report = run(&fixture);
    assert!(report.ignored_inputs.annotations);
    assert!(report.ignored_inputs.summary_requires);
    expect_refuted(&fixture, &report, fixture.obligations[0]);
}

#[test]
fn assumes_after_or_below_the_site_are_not_premises() {
    for fixture in [
        fixtures::assume_after_assert(),
        fixtures::assumes_in_later_block(),
        fixtures::contradictory_later_assume(),
    ] {
        let report = run(&fixture);
        expect_refuted(&fixture, &report, fixture.obligations[0]);
    }
}

#[test]
fn an_unsatisfiable_premise_prefix_is_refused_not_discharged() {
    let vacuous = fixtures::vacuous_prefix(0);
    let report = run(&vacuous);
    assert_eq!(
        expect_refusal(&vacuous, &report, vacuous.obligations[0]),
        &TrustIrBodyRefusal::VacuousPremises
    );
    expect_never_discharged(&vacuous, &report);

    // The twin is satisfiable by exactly `a == 0`, so the probe must NOT
    // call it vacuous.
    let twin = fixtures::vacuous_prefix(1);
    let report = run(&twin);
    let TrustIrBodyVerdict::DischargedAdvisory {
        premise_witness, ..
    } = verdict(&report, twin.obligations[0])
    else {
        panic!(
            "twin should be discharged, got {:?}",
            verdict(&report, twin.obligations[0])
        );
    };
    assert!(matches!(
        premise_witness.params[0].1,
        trust_vc_trust_engine::TrustIrScalar::Int { value: 0, .. }
    ));
}

#[test]
fn signedness_comes_from_the_type_for_overflow() {
    let unsigned = fixtures::pinned_operands_add(Ty::U8, "pinned_add_u8");
    let report = run(&unsigned);
    expect_discharged(&unsigned, &report, unsigned.obligations[0]);

    let signed = fixtures::pinned_operands_add(Ty::I8, "pinned_add_i8");
    let report = run(&signed);
    expect_refuted(&signed, &report, signed.obligations[0]);
}

#[test]
fn signedness_comes_from_the_op_for_comparisons() {
    for (ty, pinned, name) in [
        (Ty::I8, -1i128, "all_ones_i8"),
        (Ty::U8, 255i128, "all_ones_u8"),
    ] {
        let fixture = fixtures::sign_of_all_ones(ty, pinned, name);
        let report = run(&fixture);
        // 0xFF is < 0 signed ...
        expect_discharged(&fixture, &report, fixture.obligations[0]);
        // ... and never < 0 unsigned.
        expect_refuted(&fixture, &report, fixture.obligations[1]);
    }
}

#[test]
fn a_refutation_that_needs_an_earlier_assert_to_fail_is_labelled() {
    let fixture = fixtures::prior_asserts_guard_the_add();
    let report = run(&fixture);
    expect_refuted(&fixture, &report, fixture.obligations[0]);
    expect_refuted(&fixture, &report, fixture.obligations[1]);
    let add = report.obligation(fixture.obligations[2]).unwrap();
    assert_eq!(add.prior_asserts_not_assumed, 2);
    assert!(
        matches!(
            add.verdict,
            TrustIrBodyVerdict::RefutedIgnoringPriorAsserts { .. }
        ),
        "expected RefutedIgnoringPriorAsserts, got {:?}",
        add.verdict
    );
}

#[test]
fn an_assert_no_obligation_cites_is_listed_and_not_examined() {
    let fixture = fixtures::unobligated_assert_present();
    let report = run(&fixture);
    assert_eq!(report.obligations.len(), 1);
    expect_discharged(&fixture, &report, fixture.obligations[0]);
    assert_eq!(report.unobligated_asserts.len(), 1);
    assert_eq!(
        trust_vc_trust_engine::UNOBLIGATED_ASSERT_LABEL,
        "unobligated assert, not examined"
    );
}

#[test]
fn wider_widths_agree_with_the_type_bounds() {
    for (ty, bound, signed, name) in [
        (Ty::U16, 100i128, false, "guarded_add_u16"),
        (Ty::I16, 100i128, true, "guarded_add_i16"),
        (Ty::U32, 100i128, false, "guarded_add_u32"),
        (Ty::I32, 100i128, true, "guarded_add_i32"),
        (Ty::U64, 100i128, false, "guarded_add_u64"),
        (Ty::I64, 100i128, true, "guarded_add_i64"),
    ] {
        let fixture = fixtures::guarded_wide_add(ty, bound, signed, name);
        let report = run(&fixture);
        expect_discharged(&fixture, &report, fixture.obligations[0]);
    }

    // A guard that does NOT bound the sum must still refute: the wide-width
    // encoding may not over-approximate a discharge.
    for (ty, bound, signed, name) in [
        (Ty::U16, 40_000i128, false, "loose_guard_u16"),
        (Ty::I16, 30_000i128, true, "loose_guard_i16"),
        (Ty::U32, 4_000_000_000i128, false, "loose_guard_u32"),
        (
            Ty::I64,
            9_000_000_000_000_000_000i128,
            true,
            "loose_guard_i64",
        ),
    ] {
        let fixture = fixtures::guarded_wide_add(ty, bound, signed, name);
        let report = run(&fixture);
        expect_refuted(&fixture, &report, fixture.obligations[0]);
    }

    // Exactly at the boundary: MAX + 0 is fine, MAX + 1 is not.
    for (ty, lhs, rhs, refuted, name) in [
        (Ty::I16, 32767i128, 0i128, false, "pinned_i16_max_plus_zero"),
        (Ty::I16, 32767, 1, true, "pinned_i16_max_plus_one"),
        (Ty::U16, 65535, 0, false, "pinned_u16_max_plus_zero"),
        (Ty::U16, 65535, 1, true, "pinned_u16_max_plus_one"),
        (Ty::I32, 2_147_483_647, 1, true, "pinned_i32_max_plus_one"),
        (
            Ty::U64,
            18_446_744_073_709_551_615,
            1,
            true,
            "pinned_u64_max_plus_one",
        ),
        (
            Ty::I64,
            9_223_372_036_854_775_807,
            0,
            false,
            "pinned_i64_max_plus_zero",
        ),
        (
            Ty::I64,
            -9_223_372_036_854_775_808,
            0,
            false,
            "pinned_i64_min_plus_zero",
        ),
    ] {
        let fixture = fixtures::pinned_wide_add(ty, lhs, rhs, name);
        let report = run(&fixture);
        if refuted {
            expect_refuted(&fixture, &report, fixture.obligations[0]);
        } else {
            expect_discharged(&fixture, &report, fixture.obligations[0]);
        }
    }
}

// ---------------------------------------------------------------------------
// Obligation-level refusals
// ---------------------------------------------------------------------------

#[test]
fn obligations_without_a_usable_site_are_refused() {
    // site None
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.proof_obligations[0].site = None;
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::SiteMissing
    );

    // function None (the site still scopes it to this function)
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.proof_obligations[0].function = None;
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::FunctionScopeMissing
    );

    // site that is not an Assert
    let mut fixture = fixtures::guarded_checked_add_u8();
    let site = fixture.module.proof_obligations[0].site.unwrap();
    // Seven nodes before the Assert is the Overflow of the checked-op pack:
    // Overflow, Undef, InsertField, InsertField, ExtractField, Const, ICmp.
    fixture.module.proof_obligations[0].site = Some(ObligationSite::new(
        FIXTURE_FUNCTION,
        site.block,
        site.inst_index - 7,
    ));
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::SiteNotAssert { found: "Overflow" }
    );

    // index past the end
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.proof_obligations[0].site =
        Some(ObligationSite::new(FIXTURE_FUNCTION, site.block, 999));
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::SiteIndexOutOfRange {
            block: site.block,
            inst_index: 999
        }
    );

    // block that does not exist
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.proof_obligations[0].site =
        Some(ObligationSite::new(FIXTURE_FUNCTION, BlockId::new(7), 0));
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::SiteBlockMissing {
            block: BlockId::new(7)
        }
    );

    // an obligation kind this lane does not answer
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.proof_obligations[0].kind = ObligationKind::Postcondition;
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::UnsupportedObligationKind("Postcondition".to_string())
    );
}

#[test]
fn a_site_in_another_function_is_refused_from_both_sides() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let mut second = fixture.module.functions[0].clone();
    second.id = trust_ir::FuncId::new(1);
    second.name = "sibling".to_string();
    fixture.module.functions.push(second);
    let site = fixture.module.proof_obligations[0].site.unwrap();
    fixture.module.proof_obligations[0].site = Some(ObligationSite::new(
        trust_ir::FuncId::new(1),
        site.block,
        site.inst_index,
    ));

    for function in [FIXTURE_FUNCTION, trust_ir::FuncId::new(1)] {
        let report = TrustVcTrustEngine::new()
            .discharge_trust_ir_function(&fixture.module, function, &TrustIrBodyOptions::default())
            .expect("both functions are reportable");
        assert!(matches!(
            verdict(&report, fixture.obligations[0]),
            TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::SiteFunctionMismatch { .. })
        ));
    }
}

#[test]
fn a_prestamped_status_and_a_forged_certificate_change_nothing() {
    let clean = fixtures::unguarded_checked_add_u8();
    let clean_digest = trust_ir_body_semantic_digest(&clean.module, FIXTURE_FUNCTION).unwrap();

    let mut stamped = fixtures::unguarded_checked_add_u8();
    stamped.module.proof_obligations[0].status = ProofStatus::Discharged;
    stamped.module.proof_certificates.push(ProofCertificate {
        obligation: stamped.obligations[0],
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::Trusted("forged for the fixture".to_string()),
        assurance: None,
    });
    let report = run(&stamped);
    assert!(report.ignored_inputs.statuses);
    assert!(report.ignored_inputs.certificates);
    expect_refuted(&stamped, &report, stamped.obligations[0]);
    assert_eq!(report.semantic_digest, clean_digest);
}

#[test]
fn the_semantic_digest_moves_with_the_body_not_with_the_verdict() {
    let base = fixtures::guarded_checked_add_u8();
    let digest = trust_ir_body_semantic_digest(&base.module, FIXTURE_FUNCTION).unwrap();

    let mut edited = fixtures::guarded_checked_add_u8();
    edited.module.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::U8,
        value: Constant::Int(101),
    };
    assert_ne!(
        trust_ir_body_semantic_digest(&edited.module, FIXTURE_FUNCTION).unwrap(),
        digest,
        "an instruction edit must move the digest"
    );

    let mut retyped = fixtures::guarded_checked_add_u8();
    retyped.module.func_types[0].returns = vec![Ty::U16];
    assert_ne!(
        trust_ir_body_semantic_digest(&retyped.module, FIXTURE_FUNCTION).unwrap(),
        digest,
        "a function-type edit must move the digest"
    );

    let mut annotated = fixtures::guarded_checked_add_u8();
    annotated.module.functions[0].blocks[0].body[0].span = Some(trust_ir::SourceSpan {
        file: 0,
        line: 7,
        col: 3,
    });
    annotated.module.proof_obligations[0].status = ProofStatus::Failed;
    assert_eq!(
        trust_ir_body_semantic_digest(&annotated.module, FIXTURE_FUNCTION).unwrap(),
        digest,
        "debug metadata and statuses must not move the digest"
    );
}

// ---------------------------------------------------------------------------
// Function-level refusals
// ---------------------------------------------------------------------------

fn entry_insert_before_terminator(fixture: &mut Fixture, node: InstrNode) -> u32 {
    let block = &mut fixture.module.functions[0].blocks[0];
    let index = block.body.len() - 1;
    block.body.insert(index, node);
    // Every site of this suite's fixtures sits before the terminator, so the
    // obligation indices are unchanged; assert that rather than assume it.
    for obligation in &fixture.module.proof_obligations {
        if let Some(site) = obligation.site {
            assert!(
                (site.inst_index as usize) < index,
                "fixture site would shift"
            );
        }
    }
    index as u32
}

#[test]
fn every_instruction_outside_v0_refuses_the_whole_function() {
    let scratch = ValueId::new(900);
    let cases: Vec<(&'static str, Inst, Vec<ValueId>)> = vec![
        (
            "Call",
            Inst::Call {
                callee: FIXTURE_FUNCTION,
                args: vec![ValueId::new(0), ValueId::new(1)],
            },
            vec![scratch],
        ),
        (
            "Load",
            Inst::Load {
                ty: Ty::U8,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            },
            vec![scratch],
        ),
        (
            "Alloca",
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            vec![scratch],
        ),
        (
            "Store",
            Inst::Store {
                ty: Ty::U8,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                volatile: false,
                align: None,
            },
            vec![],
        ),
        (
            "DialectOp",
            Inst::DialectOp(Box::new(
                trust_ir::DialectInst::new("trust-symbolic", "aggregate")
                    .with_operand(ValueId::new(0))
                    .with_result_ty(Ty::U8),
            )),
            vec![scratch],
        ),
        (
            "BinOp",
            Inst::BinOp {
                op: trust_ir::BinOp::UDiv,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            vec![scratch],
        ),
        (
            "UnOp",
            Inst::UnOp {
                op: UnOp::Not,
                ty: Ty::Bool,
                operand: ValueId::new(0),
            },
            vec![scratch],
        ),
        (
            "Select",
            Inst::Select {
                ty: Ty::U8,
                cond: ValueId::new(0),
                then_val: ValueId::new(0),
                else_val: ValueId::new(1),
            },
            vec![scratch],
        ),
        // trust-ir v47: a drop runs a destructor, which v0 does not model.
        // It HAS a wire tag, so this is the checker's refusal, not the
        // digest's.
        (
            "Drop",
            Inst::Drop {
                ty: Ty::U8,
                ptr: ValueId::new(0),
            },
            vec![],
        ),
        // The unwinding and no-unwind twins of the call, drop and check
        // instructions: each is outside v0 exactly as its plain form is.
        (
            "CallCannotUnwind",
            Inst::CallCannotUnwind {
                callee: FIXTURE_FUNCTION,
                args: vec![ValueId::new(0), ValueId::new(1)],
            },
            vec![scratch],
        ),
        (
            "CallIndirectCannotUnwind",
            Inst::CallIndirectCannotUnwind {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
            },
            vec![scratch],
        ),
    ];

    for (name, inst, results) in cases {
        let mut fixture = fixtures::guarded_checked_add_u8();
        let index = entry_insert_before_terminator(
            &mut fixture,
            InstrNode::new(inst).with_results(results),
        );
        let report = run(&fixture);
        match report.function_refusal.as_ref() {
            Some(TrustIrBodyRefusal::UnsupportedInstruction {
                block,
                inst_index,
                inst,
                ..
            }) => {
                assert_eq!(*inst, name);
                assert_eq!(*block, BlockId::new(0));
                assert_eq!(*inst_index, index);
            }
            other => panic!("{name}: expected UnsupportedInstruction, got {other:?}"),
        }
        assert_eq!(
            expect_refusal(&fixture, &report, fixture.obligations[0]),
            report.function_refusal.as_ref().unwrap()
        );
    }

    // The unwinding twins are TERMINATORS: inside a block, each refuses the
    // whole function as control flow, naming itself.
    let terminators: Vec<(&'static str, Inst, Vec<ValueId>)> = vec![
        (
            "InvokeIndirect",
            Inst::InvokeIndirect {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
                normal_dest: BlockId::new(0),
                normal_args: vec![],
                unwind_dest: BlockId::new(0),
            },
            vec![scratch],
        ),
        (
            "DropInvoke",
            Inst::DropInvoke {
                ty: Ty::U8,
                ptr: ValueId::new(0),
                normal_dest: BlockId::new(0),
                normal_args: vec![],
                unwind_dest: BlockId::new(0),
            },
            vec![],
        ),
        (
            "AssertInvoke",
            Inst::AssertInvoke {
                cond: ValueId::new(0),
                kind: AssertKind::Unspecified,
                site: PanicSite {
                    entry: FIXTURE_FUNCTION,
                    location: PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
                },
                normal_dest: BlockId::new(0),
                normal_args: vec![],
                unwind_dest: BlockId::new(0),
            },
            vec![],
        ),
    ];
    for (name, inst, results) in terminators {
        let mut fixture = fixtures::guarded_checked_add_u8();
        let index = entry_insert_before_terminator(
            &mut fixture,
            InstrNode::new(inst).with_results(results),
        );
        let report = run(&fixture);
        match report.function_refusal.as_ref() {
            Some(TrustIrBodyRefusal::ControlFlow {
                block,
                inst_index,
                detail,
            }) => {
                assert!(detail.contains(name), "{name}: {detail}");
                assert_eq!(*block, BlockId::new(0));
                assert_eq!(*inst_index, Some(index));
            }
            other => panic!("{name}: expected ControlFlow, got {other:?}"),
        }
        expect_never_discharged(&fixture, &report);
    }
}

/// Gives every `Assert` of the fixture's function this kind and site.
fn set_every_assert(fixture: &mut Fixture, kind: AssertKind, site: Option<PanicSite>) {
    let mut set = 0;
    for block in &mut fixture.module.functions[0].blocks {
        for node in &mut block.body {
            if let Inst::Assert {
                kind: assert_kind,
                site: assert_site,
                ..
            } = &mut node.inst
            {
                *assert_kind = kind;
                *assert_site = site;
                set += 1;
            }
        }
    }
    assert!(set > 0, "{}: the fixture has an assert", fixture.name);
}

/// A check's kind names WHICH panic its failure is, never whether it fails,
/// so a kind that carries no operands reads exactly as the kindless check:
/// the discharged fixture stays discharged and its unguarded twin stays
/// refuted under every such kind.
#[test]
fn an_operand_free_assert_kind_reads_as_the_kindless_check() {
    for kind in [
        AssertKind::Overflow(AssertOverflowOp::Add),
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::NullPtr,
    ] {
        let mut fixture = fixtures::guarded_checked_add_u8();
        set_every_assert(&mut fixture, kind, None);
        let report = run(&fixture);
        assert!(
            report.function_refusal.is_none(),
            "{kind:?}: {:?}",
            report.function_refusal
        );
        expect_discharged(&fixture, &report, fixture.obligations[0]);

        let mut twin = fixtures::unguarded_checked_add_u8();
        set_every_assert(&mut twin, kind, None);
        let report = run(&twin);
        expect_refuted(&twin, &report, twin.obligations[0]);
    }
}

/// A sited check names the panic entry it calls and the location it reports,
/// and an operand-carrying kind names the values its message prints. v0
/// models neither, so either refuses the whole function at the assert, by
/// name, whatever the kind.
#[test]
fn a_sited_or_operand_carrying_assert_refuses_the_whole_function() {
    let site = PanicSite {
        entry: FIXTURE_FUNCTION,
        location: PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
    };
    for (label, kind, site) in [
        ("sited, unspecified", AssertKind::Unspecified, Some(site)),
        (
            "sited, overflow",
            AssertKind::Overflow(AssertOverflowOp::Add),
            Some(site),
        ),
        (
            "bounds_check",
            AssertKind::BoundsCheck {
                index: ValueId::new(0),
                len: ValueId::new(1),
            },
            None,
        ),
        (
            "misaligned_ptr",
            AssertKind::MisalignedPtr {
                required: ValueId::new(0),
                found: ValueId::new(1),
            },
            None,
        ),
    ] {
        let mut fixture = fixtures::guarded_checked_add_u8();
        set_every_assert(&mut fixture, kind, site);
        let report = run(&fixture);
        match report.function_refusal.as_ref() {
            Some(TrustIrBodyRefusal::UnsupportedInstruction { inst, .. }) => {
                assert_eq!(*inst, "Assert", "{label}");
            }
            other => panic!("{label}: expected UnsupportedInstruction, got {other:?}"),
        }
        expect_never_discharged(&fixture, &report);
    }
}

/// trust-ir v50's constant-size uniform array `[v; n]`, end to end through
/// the public entry: the body is digested (wire v50 encodes both spellings in
/// constant size, so it HAS a wire identity), checked, and refused as a whole
/// function, and every obligation in it carries that refusal.
///
/// The refusal must cost the same at every length. Nothing here times
/// anything: the same refusal comes back at two copies and at `u64::MAX`
/// copies, and a pass that walked `n` (digest, clone, check or report) could
/// not return at 2^64 elements. The test itself allocates nothing per element.
#[test]
fn a_uniform_array_refuses_the_whole_function_at_every_length() {
    let scratch = ValueId::new(900);
    let refusals = |len: u64| {
        [0, 1].map(|spelling| {
            let mut fixture = fixtures::guarded_checked_add_u8();
            let elem = fixture
                .module
                .add_type(Ty::U8)
                .expect("Module::add_type: test fixture");
            let array = Ty::Array(elem, len);
            let array_text = array.to_string();
            let inst = if spelling == 0 {
                Inst::ArraySplat {
                    ty: array,
                    value: ValueId::new(0),
                }
            } else {
                Inst::Const {
                    ty: array,
                    value: Constant::splat(Constant::Int(7), len),
                }
            };
            let index = entry_insert_before_terminator(
                &mut fixture,
                InstrNode::new(inst).with_results(vec![scratch]),
            );
            let digest = trust_ir_body_semantic_digest(&fixture.module, FIXTURE_FUNCTION)
                .expect("a v50 uniform array has a wire identity");
            let report = run(&fixture);
            assert_eq!(report.semantic_digest, digest);
            let refusal = report
                .function_refusal
                .clone()
                .expect("a uniform array refuses the whole function");
            assert_eq!(
                expect_refusal(&fixture, &report, fixture.obligations[0]),
                &refusal
            );
            expect_never_discharged(&fixture, &report);
            (index, digest, refusal, array_text)
        })
    };

    let small = refusals(2);
    let mut digests = std::collections::BTreeSet::new();
    for len in [2, 1 << 40, u64::MAX] {
        let [(index, register_digest, register, _), (_, typed_digest, typed, array)] =
            refusals(len);
        assert!(array.ends_with(&format!(" x {len}]")), "{array}");
        assert_eq!(
            register,
            TrustIrBodyRefusal::UnsupportedInstruction {
                block: BlockId::new(0),
                inst_index: index,
                inst: "ArraySplat",
                detail: "instruction is outside v0".to_string(),
            }
        );
        // The register refusal does not mention the length: it is the SAME
        // refusal at every length.
        assert_eq!(register, small[0].2, "len {len}");
        assert_eq!(
            typed,
            TrustIrBodyRefusal::UnsupportedType {
                block: Some(BlockId::new(0)),
                inst_index: Some(index),
                ty: array,
            }
        );
        // The length is part of the body, so it is part of what a verdict
        // would be about: distinct lengths, distinct digests.
        digests.insert(register_digest);
        digests.insert(typed_digest);
    }
    assert_eq!(
        digests.len(),
        6,
        "each spelling and length has its own digest"
    );
}

/// The constructs trust-ir carried AHEAD OF THEIR BINARY WIRE TAG until the
/// INST wire batch (wire v51) — the bulk-memory pair and the new bit/float
/// sub-ops — now have a wire identity, so the body is digested and reaches
/// the checker, which refuses each BY NAME as outside v0. Never discharged,
/// and never a panic out of `Module::stable_digest`.
///
/// The bulk-memory pair is the case that matters for soundness: v0 models no
/// memory, so a verdict about a body that copies or fills memory could only
/// be about some other program.
#[test]
fn the_inst_wire_batch_constructs_are_refused_by_name() {
    let scratch = ValueId::new(900);
    let cases: Vec<(&'static str, Inst, Vec<ValueId>)> = vec![
        (
            "MemCopy",
            Inst::MemCopy {
                dst: ValueId::new(0),
                src: ValueId::new(1),
                bytes: ValueId::new(0),
                overlap: false,
            },
            vec![],
        ),
        (
            "MemCopy",
            Inst::MemCopy {
                dst: ValueId::new(0),
                src: ValueId::new(1),
                bytes: ValueId::new(0),
                overlap: true,
            },
            vec![],
        ),
        (
            "MemSet",
            Inst::MemSet {
                dst: ValueId::new(0),
                byte: ValueId::new(1),
                bytes: ValueId::new(0),
            },
            vec![],
        ),
        (
            "UnOp",
            Inst::UnOp {
                op: UnOp::CtLz,
                ty: Ty::U8,
                operand: ValueId::new(0),
            },
            vec![scratch],
        ),
        (
            "BinOp",
            Inst::BinOp {
                op: trust_ir::BinOp::RotL,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            vec![scratch],
        ),
    ];

    for (name, inst, results) in cases {
        let mut fixture = fixtures::guarded_checked_add_u8();
        let index = entry_insert_before_terminator(
            &mut fixture,
            InstrNode::new(inst).with_results(results),
        );
        assert!(
            trust_ir_body_semantic_digest(&fixture.module, fixture.function()).is_ok(),
            "{name}: the construct has a wire identity at this pin"
        );
        let report = run(&fixture);
        match report.function_refusal.as_ref() {
            Some(TrustIrBodyRefusal::UnsupportedInstruction {
                block,
                inst_index,
                inst,
                ..
            }) => {
                assert_eq!(*inst, name);
                assert_eq!(*block, BlockId::new(0));
                assert_eq!(*inst_index, index);
            }
            other => panic!("{name}: expected UnsupportedInstruction, got {other:?}"),
        }
        expect_never_discharged(&fixture, &report);
    }
}

/// `ProofObligation::spec` (trust-ir wire v46) names a TEMPORAL PROPERTY the
/// obligation discharges. An `Assert`-site answer cannot back that
/// attribution, so the obligation is refused — even on the panic-class kind
/// the lane otherwise answers, which is the shape an unvalidated module can
/// carry (trust-ir's validator admits `spec` only on the temporal kinds).
#[test]
fn an_obligation_naming_a_temporal_property_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    // Control: without the attribution this exact obligation is discharged.
    expect_discharged(&fixture, &run(&fixture), fixture.obligations[0]);

    fixture.module.proof_obligations[0].spec = Some(trust_ir::proof::SpecObligationRef::new(
        "Clock",
        "EventuallyTicks",
    ));
    let report = run(&fixture);
    assert_eq!(
        expect_refusal(&fixture, &report, fixture.obligations[0]),
        &TrustIrBodyRefusal::TemporalPropertyAttributed {
            machine: "Clock".to_string(),
            temporal: "EventuallyTicks".to_string(),
        }
    );
    expect_never_discharged(&fixture, &report);
}

#[test]
fn branchy_control_flow_refuses_the_whole_function() {
    // CondBr in place of the chain's Br.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let block = &mut fixture.module.functions[0].blocks[0];
        let last = block.body.len() - 1;
        let cond = match block.body[last - 1].inst {
            Inst::Assert { cond, .. } => cond,
            ref other => panic!("fixture shape changed: {other:?}"),
        };
        block.body[last] = InstrNode::new(Inst::CondBr {
            cond,
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(1),
            else_args: vec![],
        });
    }
    let report = run(&fixture);
    assert!(
        matches!(
            report.function_refusal,
            Some(TrustIrBodyRefusal::ControlFlow { .. })
        ),
        "{:?}",
        report.function_refusal
    );
    expect_never_discharged(&fixture, &report);

    // A back edge to the entry.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let blocks = &mut fixture.module.functions[0].blocks;
        let exit = blocks[1].body.len() - 1;
        blocks[1].body[exit] = InstrNode::new(Inst::Br {
            target: BlockId::new(0),
            args: vec![],
        });
    }
    let report = run(&fixture);
    assert!(matches!(
        report.function_refusal,
        Some(TrustIrBodyRefusal::ControlFlow { .. })
    ));

    // A second predecessor for the exit block.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let mut extra = Block::new(BlockId::new(2));
        extra.body.push(InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }));
        fixture.module.functions[0].blocks.push(extra);
    }
    let report = run(&fixture);
    match report.function_refusal.as_ref() {
        Some(TrustIrBodyRefusal::ControlFlow { block, detail, .. }) => {
            assert_eq!(*block, BlockId::new(1));
            assert!(detail.contains("predecessors"), "{detail}");
        }
        other => panic!("expected a predecessor refusal, got {other:?}"),
    }

    // An unreachable block.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let mut extra = Block::new(BlockId::new(2));
        extra
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        fixture.module.functions[0].blocks.push(extra);
    }
    let report = run(&fixture);
    match report.function_refusal.as_ref() {
        Some(TrustIrBodyRefusal::ControlFlow { block, detail, .. }) => {
            assert_eq!(*block, BlockId::new(2));
            assert!(detail.contains("predecessor"), "{detail}");
        }
        other => panic!("expected an unreachable-block refusal, got {other:?}"),
    }

    // A block that does not end in a terminator.
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.functions[0].blocks[1].body.pop();
    let report = run(&fixture);
    assert!(matches!(
        report.function_refusal,
        Some(TrustIrBodyRefusal::ControlFlow { .. })
    ));

    // A terminator in the middle of a block.
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let report = run(&fixture);
    assert!(matches!(
        report.function_refusal,
        Some(TrustIrBodyRefusal::ControlFlow { .. })
    ));
}

#[test]
fn ill_typed_and_malformed_bodies_refuse_the_whole_function() {
    let scratch = ValueId::new(900);

    // An Assert on a non-Bool value.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Assert {
            cond: ValueId::new(0),
            kind: AssertKind::Unspecified,
            site: None,
        }),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // An ICmp whose operands do not have the instruction's type.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::U16,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // An Overflow with a single result.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U8,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // A BinOp whose type does not match its operands.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::U16,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // An integer constant outside its type.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(300),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // An integer constant at Bool.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Int(1),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // A Br arg count the target does not declare.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let block = &mut fixture.module.functions[0].blocks[0];
        let last = block.body.len() - 1;
        block.body[last] = InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![ValueId::new(0)],
        });
    }
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));

    // A use before its definition.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: ValueId::new(901),
        })
        .with_result(scratch),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::Malformed { .. })
    ));

    // An SSA value defined twice.
    let mut fixture = fixtures::guarded_checked_add_u8();
    entry_insert_before_terminator(
        &mut fixture,
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(0)),
    );
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::Malformed { .. })
    ));

    // Entry parameters that disagree with the function type.
    let mut fixture = fixtures::guarded_checked_add_u8();
    fixture.module.functions[0].blocks[0].params.pop();
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::Malformed { .. })
    ));

    // A Return whose arity disagrees with the function type.
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        let blocks = &mut fixture.module.functions[0].blocks;
        let last = blocks[1].body.len() - 1;
        blocks[1].body[last] = InstrNode::new(Inst::Return { values: vec![] });
    }
    assert!(matches!(
        run(&fixture).function_refusal,
        Some(TrustIrBodyRefusal::IllTyped { .. })
    ));
}

#[test]
fn types_outside_v0_refuse_the_whole_function() {
    for ty in [Ty::Usize, Ty::U128, Ty::Char, Ty::I128, Ty::Isize] {
        let mut fixture = fixtures::guarded_checked_add_u8();
        fixture.module.func_types[0].params = vec![ty.clone(), Ty::U8];
        fixture.module.functions[0].blocks[0].params[0].1 = ty.clone();
        let report = run(&fixture);
        match report.function_refusal.as_ref() {
            Some(TrustIrBodyRefusal::UnsupportedType { ty: refused, .. }) => {
                assert_eq!(*refused, ty.to_string());
            }
            other => panic!("{ty}: expected UnsupportedType, got {other:?}"),
        }
        expect_never_discharged(&fixture, &report);
    }
}

#[test]
fn an_unset_tuple_field_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    {
        // Drop the InsertField that writes field 1, leaving the read unset.
        let block = &mut fixture.module.functions[0].blocks[0];
        let position = block
            .body
            .iter()
            .position(|node| matches!(node.inst, Inst::InsertField { field: 1, .. }))
            .expect("fixture packs field 1");
        let replaced = match &block.body[position].inst {
            Inst::InsertField { aggregate, .. } => *aggregate,
            other => panic!("{other:?}"),
        };
        let result = block.body[position].results[0];
        block.body[position] = InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(901));
        // Re-point the ExtractField at the partially built aggregate.
        for node in block.body.iter_mut() {
            if let Inst::ExtractField { aggregate, .. } = &mut node.inst {
                if *aggregate == result {
                    *aggregate = replaced;
                }
            }
        }
    }
    let report = run(&fixture);
    match report.function_refusal.as_ref() {
        Some(TrustIrBodyRefusal::UnsupportedInstruction { inst, detail, .. }) => {
            assert_eq!(*inst, "ExtractField");
            assert!(detail.contains("never inserted"), "{detail}");
        }
        other => panic!("expected an unset-field refusal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Lane-level errors
// ---------------------------------------------------------------------------

#[test]
fn lane_level_misuse_is_an_error_not_a_verdict() {
    let fixture = fixtures::guarded_checked_add_u8();
    let engine = TrustVcTrustEngine::new();

    for policy in [
        TrustProofPolicy::RequireReplayableCertificate,
        TrustProofPolicy::RequireStrictReplayableCertificate,
        TrustProofPolicy::RequireReleaseAdmissibleCertificate,
    ] {
        let error = engine
            .discharge_trust_ir_function(
                &fixture.module,
                FIXTURE_FUNCTION,
                &TrustIrBodyOptions {
                    proof_policy: policy,
                },
            )
            .expect_err("an advisory lane cannot promise admission");
        assert_eq!(error, TrustIrBodyError::UnsupportedPolicy(policy));
    }

    let missing = trust_ir::FuncId::new(9);
    assert_eq!(
        engine
            .discharge_trust_ir_function(&fixture.module, missing, &TrustIrBodyOptions::default())
            .expect_err("no such function"),
        TrustIrBodyError::FunctionMissing(missing)
    );

    let mut duplicated = fixtures::guarded_checked_add_u8();
    let clone = duplicated.module.functions[0].clone();
    duplicated.module.functions.push(clone);
    assert_eq!(
        engine
            .discharge_trust_ir_function(
                &duplicated.module,
                FIXTURE_FUNCTION,
                &TrustIrBodyOptions::default()
            )
            .expect_err("duplicated function"),
        TrustIrBodyError::FunctionDuplicated(FIXTURE_FUNCTION)
    );

    let mut duplicate_ids = fixtures::guarded_checked_add_u8();
    let obligation = duplicate_ids.module.proof_obligations[0].clone();
    duplicate_ids.module.proof_obligations.push(obligation);
    assert_eq!(
        engine
            .discharge_trust_ir_function(
                &duplicate_ids.module,
                FIXTURE_FUNCTION,
                &TrustIrBodyOptions::default()
            )
            .expect_err("duplicate proof id"),
        TrustIrBodyError::DuplicateProofId(ProofId::new(0))
    );
}

// ---------------------------------------------------------------------------
// The serialized path is untouched
// ---------------------------------------------------------------------------

const NATIVE_REQUEST_TRUST_BUNDLE: &str =
    include_str!("../fixtures/trust_ir_native/native_request_trust_bundle.json");

/// The in-process lane does NOT open the serialized door: a bundle asking
/// trust-vc to discharge obligations is still refused, with or without the
/// body-lane module in it.
#[test]
fn the_serialized_discharge_request_is_still_refused() {
    let engine = TrustVcTrustEngine::new();

    let mut bundle: NativeVerificationBundle =
        serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE).expect("fixture decodes");
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.mode = trust_ir::request::TrustVcVerificationMode::DischargeProofObligations;
        request.certificates.clear();
    } else {
        panic!("fixture's first request should be TrustVc");
    }
    engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a serialized discharge request must still fail loudly");

    // The same, with a body-lane module swapped in: still an error, never a
    // verdict.
    let fixture = fixtures::guarded_checked_add_u8();
    let mut bundle: NativeVerificationBundle =
        serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE).expect("fixture decodes");
    bundle.module = fixture.module.clone();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.mode = trust_ir::request::TrustVcVerificationMode::DischargeProofObligations;
        request.certificates.clear();
        request.obligations = vec![fixture.obligations[0]];
    }
    engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a serialized discharge request must still fail loudly");
}

// ---------------------------------------------------------------------------
// Fixture round-trip
// ---------------------------------------------------------------------------

const GUARDED_CHECKED_ADD_U8_JSON: &str =
    include_str!("../fixtures/trust_ir_body/guarded_checked_add_u8.json");

/// The checked-in JSON is the builder's own output. Regenerate with
/// `TRUST_VC_REGEN_TRUST_IR_BODY_FIXTURES=1`.
#[test]
fn the_checked_in_fixture_matches_the_builder() {
    let fixture = fixtures::guarded_checked_add_u8();
    let rendered = serde_json::to_string_pretty(&fixture.module).expect("module serializes");
    if std::env::var_os("TRUST_VC_REGEN_TRUST_IR_BODY_FIXTURES").is_some() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/fixtures/trust_ir_body/guarded_checked_add_u8.json"
        );
        let bytes = format!("{rendered}\n");
        if std::fs::read(path).ok().as_deref() != Some(bytes.as_bytes()) {
            std::fs::write(path, bytes).expect("fixture is writable");
        }
    }
    // The fixture README says the builder reproduces the file byte for byte at
    // the pin; this is the check that makes the claim true.
    assert_eq!(
        format!("{rendered}\n"),
        GUARDED_CHECKED_ADD_U8_JSON,
        "checked-in fixture bytes drifted from the builder's serde rendering"
    );
    let decoded: trust_ir::Module =
        serde_json::from_str(GUARDED_CHECKED_ADD_U8_JSON).expect("checked-in fixture decodes");
    assert_eq!(decoded, fixture.module, "checked-in fixture is stale");
    assert_eq!(
        trust_ir_body_semantic_digest(&decoded, FIXTURE_FUNCTION).unwrap(),
        trust_ir_body_semantic_digest(&fixture.module, FIXTURE_FUNCTION).unwrap()
    );
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(&decoded, FIXTURE_FUNCTION, &TrustIrBodyOptions::default())
        .expect("decoded fixture is reportable");
    assert!(report.obligations[0].verdict.is_discharged_advisory());
}

// ---------------------------------------------------------------------------
// The `Undef` havoc reading: measured, disclosed, and contained
// ---------------------------------------------------------------------------

fn interpret_raw(fixture: &Fixture, args: &[(Ty, i128)]) -> Result<(), trust_ir::InterpretError> {
    let args = args
        .iter()
        .map(|(ty, value)| trust_ir::InterpretValue::int(ty.clone(), *value).expect("in range"))
        .collect::<Vec<_>>();
    trust_ir::Interpreter::with_module(&fixture.module)
        .execute_func(FIXTURE_FUNCTION, args)
        .map(|_| ())
}

/// The fact the lane must never hide: Trust's real checked-op pack seeds its
/// tuple with `Inst::Undef`, and the PINNED reference interpreter
/// (trust-ir@4f09dab8 `interpret.rs:1194` -> `scalar_poison`) calls executing
/// one at a TUPLE type undefined behaviour. So on the module AS WRITTEN no
/// input reaches the site at all, and the discharge is about the
/// havoc-instantiated body instead. That is a disclosed reading, not a
/// repaired one.
#[test]
fn the_real_checked_op_pack_is_undefined_behaviour_under_the_pinned_interpreter() {
    let fixture = fixtures::guarded_checked_add_u8();
    let error = interpret_raw(&fixture, &[(Ty::U8, 1), (Ty::U8, 1)])
        .expect_err("the module as written is not executable");
    assert_eq!(
        error.code,
        trust_ir::InterpretErrorCode::UndefinedBehavior,
        "the pinned interpreter must refuse to execute Undef: {error:?}"
    );
    assert!(
        error.message.contains("undef"),
        "the UB must be the Undef seed, not something else: {error:?}"
    );

    let report = run(&fixture);
    assert!(
        report.obligations[0].verdict.is_discharged_advisory(),
        "the lane still decides the havoc reading"
    );
    assert_eq!(
        report.obligations[0].reading,
        BodyReading::HavocInstantiatedUndef,
        "and must say so on the obligation"
    );
    assert_eq!(
        report.havoc_seeds.len(),
        1,
        "and must list the seed it instantiated: {:?}",
        report.havoc_seeds
    );
    assert_eq!(report.havoc_seeds[0].ty, "(u8, bool)");
    assert!(HAVOC_INSTANTIATION_NOTE.contains("undefined behaviour"));
}

/// The disclosure travels with the witness, not only with the report.
#[test]
fn every_witness_carries_the_reading_it_was_replayed_under() {
    let havoc = fixtures::unguarded_checked_add_u8();
    let report = run(&havoc);
    match verdict(&report, havoc.obligations[0]) {
        TrustIrBodyVerdict::Refuted { witness } => assert_eq!(
            witness.reading,
            BodyReading::HavocInstantiatedUndef,
            "a refutation behind the pack is a counterexample of the HAVOC reading only"
        ),
        other => panic!("expected Refuted, got {other:?}"),
    }

    // A body with no `Undef` anywhere is decided on the module as written.
    let pinned = fixtures::wraparound_semantics();
    let report = run(&pinned);
    assert!(
        report.havoc_seeds.is_empty(),
        "no pack, no seed: {:?}",
        report.havoc_seeds
    );
    for obligation in &report.obligations {
        assert_eq!(
            obligation.reading,
            BodyReading::PinnedInterpreter,
            "{:?} is about the module as written",
            obligation.proof_id
        );
    }
    match verdict(&report, pinned.obligations[0]) {
        TrustIrBodyVerdict::DischargedAdvisory {
            premise_witness, ..
        } => assert_eq!(premise_witness.reading, BodyReading::PinnedInterpreter),
        other => panic!("expected DischargedAdvisory, got {other:?}"),
    }
    match verdict(&report, pinned.obligations[1]) {
        TrustIrBodyVerdict::Refuted { witness } => {
            assert_eq!(witness.reading, BodyReading::PinnedInterpreter);
            // The pinned reading means exactly this: the witness is a
            // counterexample of the module the obligation is about.
            let args = witness
                .params
                .iter()
                .map(|(_, scalar)| match scalar {
                    trust_vc_trust_engine::TrustIrScalar::Int { ty, value } => (ty.clone(), *value),
                    other => panic!("unexpected witness scalar {other:?}"),
                })
                .collect::<Vec<_>>();
            let error = interpret_raw(&pinned, &args)
                .expect_err("the witness must fail the module as written");
            assert_eq!(error.code, trust_ir::InterpretErrorCode::Panic);
        }
        other => panic!("expected Refuted, got {other:?}"),
    }
}

/// What makes the havoc admission an over-approximation rather than a guess:
/// a havoc value is UNREADABLE. trust-ir's own `FreshSymbolicHavoc` doc
/// (`proof/annotations.rs:168-178`) requires exactly this of a consumer, and
/// the lane keeps it structurally instead of trusting the annotation.
#[test]
fn a_havoc_field_can_never_be_observed() {
    // Reading a field no `InsertField` wrote is refused ...
    let fixture = fixtures::extract_uninserted_field();
    let report = run(&fixture);
    match report
        .function_refusal
        .as_ref()
        .expect("the body must be refused")
    {
        TrustIrBodyRefusal::UnsupportedInstruction { inst, detail, .. } => {
            assert_eq!(*inst, "ExtractField");
            assert!(
                detail.contains("havoc"),
                "the refusal must name the reason: {detail}"
            );
        }
        other => panic!("expected UnsupportedInstruction, got {other:?}"),
    }
    assert!(
        report.havoc_seeds.is_empty(),
        "a refused body discloses no seeds"
    );

    // ... and so is every other route out of the aggregate.
    for fixture in [
        fixtures::copy_the_pack(),
        fixtures::return_the_pack(),
        fixtures::assume_on_the_pack(),
    ] {
        let report = run(&fixture);
        assert!(
            report.function_refusal.is_some(),
            "{}: a havoc aggregate must not escape as a scalar",
            fixture.name
        );
        for obligation in &report.obligations {
            assert!(
                matches!(obligation.verdict, TrustIrBodyVerdict::NotAnswerable(_)),
                "{}: {obligation:?}",
                fixture.name
            );
        }
    }
}
