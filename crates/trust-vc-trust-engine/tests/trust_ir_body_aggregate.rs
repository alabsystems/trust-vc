// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Complete scalar tuples use the shared IR's declaration order and replay as written.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, Fx};
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_ir::{ICmpOp, Inst, InstrNode, ObligationKind, OverflowOp, Ty, ValueId};
use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, BodyReading, LoweringWitness, TrustIrBodyAuthority,
    TrustIrBodyOptions, TrustIrBodyRefusal, TrustIrBodyReport, TrustIrBodyVerdict,
    TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

fn aggregate(fx: &mut Fx, ty: Ty, fields: &[ValueId]) -> ValueId {
    let result = fx.fresh();
    fx.push(
        InstrNode::new(Inst::MakeAggregate {
            ty,
            variant: None,
            fields: fields.to_vec(),
        })
        .with_result(result),
    );
    result
}

fn checked_add(guarded: bool) -> Fixture {
    let (mut fx, args) = Fx::new("complete_checked_add", &[Ty::U8, Ty::U8], &[Ty::U8]);
    if guarded {
        fx.requires(args[0], ICmpOp::Ult, Ty::U8, 100);
        fx.requires(args[1], ICmpOp::Ult, Ty::U8, 100);
    }
    let value = fx.fresh();
    let flag = fx.fresh();
    fx.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U8,
            lhs: args[0],
            rhs: args[1],
        })
        .with_result(value)
        .with_result(flag),
    );
    let tuple = aggregate(&mut fx, Ty::Tuple(vec![Ty::U8, Ty::Bool]), &[value, flag]);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let sum = fx.extract(Ty::U8, tuple, 0);
    fx.ret(&[sum]);
    fx.finish()
}

fn ordered_tuple(claim_second: bool) -> Fixture {
    let (mut fx, args) = Fx::new("ordered_tuple", &[Ty::U64, Ty::U64], &[]);
    let tuple = aggregate(&mut fx, Ty::Tuple(vec![Ty::U64, Ty::U64]), &args);
    let first = fx.extract(Ty::U64, tuple, 0);
    let expected = args[usize::from(claim_second)];
    let condition = fx.icmp(ICmpOp::Eq, Ty::U64, first, expected);
    fx.assert_obligated(condition, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

fn run(fixture: &Fixture) -> TrustIrBodyReport {
    TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions::default(),
        )
        .expect("body admission returns a report")
}

fn verdict(report: &TrustIrBodyReport) -> &TrustIrBodyVerdict {
    assert_eq!(report.obligations.len(), 1);
    &report.obligations[0].verdict
}

fn assert_pinned_advisory(report: &TrustIrBodyReport) {
    assert_eq!(report.authority, TrustIrBodyAuthority::Advisory);
    assert_eq!(report.lowering_witness, LoweringWitness::None);
    assert!(report.havoc_seeds.is_empty());
    assert_eq!(
        report.obligations[0].reading,
        BodyReading::PinnedInterpreter
    );
}

#[test]
fn complete_checked_pack_discharges_without_havoc() {
    let fixture = checked_add(true);
    let report = run(&fixture);
    assert!(report.function_refusal.is_none(), "{report:?}");
    let TrustIrBodyVerdict::DischargedAdvisory {
        premise_witness, ..
    } = verdict(&report)
    else {
        panic!("expected advisory discharge: {report:?}");
    };
    assert_eq!(premise_witness.reading, BodyReading::PinnedInterpreter);
    assert_pinned_advisory(&report);
}

#[test]
fn complete_checked_pack_false_claim_replays_overflow() {
    // The positive's only semantic change is removal of its source guards.
    let fixture = checked_add(false);
    let report = run(&fixture);
    let TrustIrBodyVerdict::Refuted { witness } = verdict(&report) else {
        panic!("unguarded u8 addition must be refuted: {report:?}");
    };
    assert_eq!(witness.reading, BodyReading::PinnedInterpreter);
    assert_pinned_advisory(&report);
}

#[test]
fn complete_tuple_preserves_full_width_field_order_and_false_claim() {
    let positive = ordered_tuple(false);
    let report = run(&positive);
    assert!(verdict(&report).is_discharged_advisory(), "{report:?}");
    assert_pinned_advisory(&report);

    // Change only which declared field the claim names.
    let negative = ordered_tuple(true);
    let report = run(&negative);
    assert!(
        matches!(verdict(&report), TrustIrBodyVerdict::Refuted { .. }),
        "{report:?}"
    );
    assert_pinned_advisory(&report);
}

#[test]
fn complete_tuple_body_mutation_changes_binding_and_is_refuted() {
    let mut fixture = ordered_tuple(false);
    let before = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
    let Inst::MakeAggregate { fields, .. } =
        &mut fixture.module.functions[0].blocks[0].body[0].inst
    else {
        panic!("fixture begins with its complete tuple");
    };
    fields.swap(0, 1);
    let after = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
    assert_ne!(before, after);
    let report = run(&fixture);
    assert!(
        matches!(verdict(&report), TrustIrBodyVerdict::Refuted { .. }),
        "{report:?}"
    );
    assert_pinned_advisory(&report);
}

#[test]
fn complete_tuple_refuses_wrong_count_type_variant_and_result_arity() {
    for mutation in 0..6 {
        let mut fixture = checked_add(true);
        let node = fixture.module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::MakeAggregate { .. }))
            .unwrap();
        let Inst::MakeAggregate {
            fields, variant, ..
        } = &mut node.inst
        else {
            unreachable!();
        };
        match mutation {
            0 => {
                fields.pop();
            }
            1 => fields.swap(0, 1),
            2 => *variant = Some(0),
            3 => {
                node.results.clear();
            }
            4 => fields[0] = ValueId::new(u32::MAX),
            5 => node.results[0] = ValueId::new(0),
            _ => unreachable!(),
        }
        let report = run(&fixture);
        assert!(
            matches!(verdict(&report), TrustIrBodyVerdict::NotAnswerable(_)),
            "case {mutation}: {report:?}"
        );
        assert!(
            matches!(
                report.function_refusal,
                Some(TrustIrBodyRefusal::IllTyped { .. } | TrustIrBodyRefusal::Malformed { .. })
            ),
            "case {mutation}: {report:?}"
        );
    }
}

#[test]
fn complete_tuple_refuses_empty_nested_and_unsupported_scalar_types() {
    for ty in [
        Ty::Tuple(vec![]),
        Ty::Tuple(vec![Ty::Tuple(vec![Ty::U8])]),
        Ty::Tuple(vec![Ty::U128, Ty::Bool]),
        Ty::U8,
    ] {
        let mut fixture = checked_add(true);
        let node = fixture.module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::MakeAggregate { .. }))
            .unwrap();
        let Inst::MakeAggregate { ty: declared, .. } = &mut node.inst else {
            unreachable!();
        };
        *declared = ty;
        let report = run(&fixture);
        assert!(
            matches!(verdict(&report), TrustIrBodyVerdict::NotAnswerable(_)),
            "{report:?}"
        );
        assert!(
            matches!(
                report.function_refusal,
                Some(TrustIrBodyRefusal::UnsupportedInstruction {
                    inst: "MakeAggregate",
                    ..
                })
            ),
            "{report:?}"
        );
    }
}

#[test]
fn complete_tuple_preserves_unsigned_max_signed_min_and_bool() {
    let (mut fx, _) = Fx::new("tuple_boundaries", &[], &[]);
    let unsigned = fx.konst(Ty::U64, i128::from(u64::MAX));
    let signed = fx.konst(Ty::I64, i128::from(i64::MIN));
    let boolean = fx.bool_const(true);
    let types = [Ty::U64, Ty::I64, Ty::Bool];
    let values = [unsigned, signed, boolean];
    let tuple = aggregate(&mut fx, Ty::Tuple(types.to_vec()), &values);
    for (field, (ty, expected)) in (0_u32..).zip(types.into_iter().zip(values)) {
        let actual = fx.extract(ty.clone(), tuple, field);
        let condition = fx.icmp(ICmpOp::Eq, ty, actual, expected);
        fx.assert_obligated(condition, ObligationKind::ArithmeticSafety);
    }
    fx.ret(&[]);
    let report = run(&fx.finish());
    assert_eq!(report.obligations.len(), 3);
    for obligation in &report.obligations {
        assert!(obligation.verdict.is_discharged_advisory(), "{report:?}");
        assert_eq!(obligation.reading, BodyReading::PinnedInterpreter);
    }
    assert_pinned_advisory(&report);
}

#[test]
fn complete_tuple_native_in_process_answer_cannot_become_authority() {
    let fixture = checked_add(true);
    let request = TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: fixture.obligations.clone(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: Some(fixture.function()),
    };
    let report = TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&fixture.module, &request)
        .expect("complete tuple reaches the existing advisory entry");
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargedAdvisory
    );
    assert!(!report.verdict().is_ok());
    assert!(report.proof_evidence().is_empty());
    assert!(report.admit_native_proof_artifacts().is_empty());
    assert!(report.discharge().is_empty());
    assert!(report.advisory_discharge().is_some());
}
