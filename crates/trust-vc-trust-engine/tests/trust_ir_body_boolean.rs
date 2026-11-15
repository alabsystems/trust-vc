// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The shared IR's explicit scalar Bool connectives retain their exact truth tables.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, Fx};
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_ir::{BinOp, ICmpOp, Inst, InstrNode, ObligationKind, OverflowOp, Ty, UnOp, ValueId};
use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, BodyReading, LoweringWitness, TrustIrBodyAuthority,
    TrustIrBodyOptions, TrustIrBodyRefusal, TrustIrBodyReport, TrustIrBodyVerdict,
    TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

const CONNECTIVES: [BinOp; 3] = [BinOp::BAnd, BinOp::BOr, BinOp::BXor];

fn claim(fx: &mut Fx, result: ValueId, expected: ValueId) {
    let condition = fx.icmp(ICmpOp::Eq, Ty::Bool, result, expected);
    fx.assert_obligated(condition, ObligationKind::ArithmeticSafety);
}

fn truth_table(op: BinOp, lhs: bool, rhs: bool, false_claim: bool) -> Fixture {
    let (mut fx, _) = Fx::new("bool_truth_table", &[], &[]);
    let a = fx.bool_const(lhs);
    let b = fx.bool_const(rhs);
    let result = fx.binop(op, Ty::Bool, a, b);
    let expected = match op {
        BinOp::BAnd => lhs && rhs,
        BinOp::BOr => lhs || rhs,
        BinOp::BXor => lhs ^ rhs,
        _ => panic!("fixture requires an explicit Bool connective"),
    };
    let expected = fx.bool_const(expected ^ false_claim);
    claim(&mut fx, result, expected);
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
    assert_eq!(report.authority, TrustIrBodyAuthority::Advisory);
    assert_eq!(report.lowering_witness, LoweringWitness::None);
    assert!(report.havoc_seeds.is_empty());
    assert_eq!(
        report.obligations[0].reading,
        BodyReading::PinnedInterpreter
    );
    &report.obligations[0].verdict
}

#[test]
fn explicit_bool_truth_tables_and_each_false_twin_replay() {
    for op in CONNECTIVES {
        for lhs in [false, true] {
            for rhs in [false, true] {
                for false_claim in [false, true] {
                    let fixture = truth_table(op, lhs, rhs, false_claim);
                    let report = run(&fixture);
                    if false_claim {
                        let TrustIrBodyVerdict::Refuted { witness } = verdict(&report) else {
                            panic!("{op:?} {lhs} {rhs}: {report:?}");
                        };
                        assert_eq!(witness.reading, BodyReading::PinnedInterpreter);
                    } else {
                        assert!(verdict(&report).is_discharged_advisory(), "{report:?}");
                    }
                }
            }
        }
    }
}

#[test]
fn symbolic_bool_identities_and_false_twins() {
    for op in CONNECTIVES {
        for false_claim in [false, true] {
            let (mut fx, args) = Fx::new("bool_identity", &[Ty::Bool], &[]);
            let result = fx.binop(op, Ty::Bool, args[0], args[0]);
            let expected = if op == BinOp::BXor {
                fx.bool_const(false)
            } else {
                args[0]
            };
            let expected = if false_claim {
                let yes = fx.bool_const(true);
                fx.binop(BinOp::BXor, Ty::Bool, expected, yes)
            } else {
                expected
            };
            claim(&mut fx, result, expected);
            fx.ret(&[]);
            let report = run(&fx.finish());
            assert_eq!(
                verdict(&report).is_discharged_advisory(),
                !false_claim,
                "{report:?}"
            );
            if false_claim {
                assert!(
                    matches!(verdict(&report), TrustIrBodyVerdict::Refuted { .. }),
                    "{report:?}"
                );
            }
        }
    }
}

#[test]
fn bool_guard_and_negation_compose_with_checked_integer_arithmetic() {
    for false_claim in [false, true] {
        let (mut fx, args) = Fx::new("bool_checked_guard", &[Ty::U8, Ty::U8], &[]);
        let bound = fx.konst(Ty::U8, 100);
        let left = fx.icmp(ICmpOp::Ult, Ty::U8, args[0], bound);
        let right = fx.icmp(ICmpOp::Ult, Ty::U8, args[1], bound);
        let guard = fx.binop(BinOp::BAnd, Ty::Bool, left, right);
        fx.assume(guard);
        let value = fx.fresh();
        let overflow = fx.fresh();
        fx.push(
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::U8,
                lhs: args[0],
                rhs: args[1],
            })
            .with_result(value)
            .with_result(overflow),
        );
        let yes = fx.bool_const(true);
        let safe = fx.binop(BinOp::BXor, Ty::Bool, overflow, yes);
        fx.assert_obligated(
            if false_claim { overflow } else { safe },
            ObligationKind::ArithmeticSafety,
        );
        fx.ret(&[]);
        let report = run(&fx.finish());
        if false_claim {
            assert!(
                matches!(verdict(&report), TrustIrBodyVerdict::Refuted { .. }),
                "{report:?}"
            );
        } else {
            assert!(verdict(&report).is_discharged_advisory(), "{report:?}");
        }
    }
}

#[test]
fn bool_contradictory_assumptions_never_discharge_a_false_claim() {
    let (mut fx, args) = Fx::new("bool_contradiction", &[Ty::Bool], &[]);
    let yes = fx.bool_const(true);
    let no = fx.bool_const(false);
    let negated = fx.binop(BinOp::BXor, Ty::Bool, args[0], yes);
    let contradiction = fx.binop(BinOp::BAnd, Ty::Bool, args[0], negated);
    fx.assume(contradiction);
    fx.assert_obligated(no, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    let report = run(&fx.finish());
    assert_eq!(
        verdict(&report),
        &TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::VacuousPremises)
    );
}

#[test]
fn bool_body_mutation_changes_identity_and_refutes_original_claim() {
    let mut fixture = truth_table(BinOp::BAnd, true, false, false);
    let before = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
    let Inst::BinOp { op, .. } = &mut fixture.module.functions[0].blocks[0].body[2].inst else {
        panic!("fixture contains its connective");
    };
    *op = BinOp::BOr;
    let after = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
    assert_ne!(before, after);
    let report = run(&fixture);
    assert!(
        matches!(verdict(&report), TrustIrBodyVerdict::Refuted { .. }),
        "{report:?}"
    );
}

#[test]
fn bool_connectives_refuse_malformed_types_operands_and_arity() {
    for mutation in 0..6 {
        let mut fixture = truth_table(BinOp::BAnd, true, false, false);
        let body = &mut fixture.module.functions[0].blocks[0].body;
        if mutation == 5 {
            body[0].inst = Inst::Const {
                ty: Ty::U8,
                value: trust_ir::Constant::Int(1),
            };
        }
        let node = &mut body[2];
        let Inst::BinOp { ty, lhs, rhs, .. } = &mut node.inst else {
            unreachable!()
        };
        match mutation {
            0 => *ty = Ty::U8,
            1 => *lhs = ValueId::new(u32::MAX),
            2 => *rhs = node.results[0],
            3 => node.results.clear(),
            4 => node.results.push(ValueId::new(100)),
            5 => {}
            _ => unreachable!(),
        }
        let report = run(&fixture);
        assert!(
            matches!(verdict(&report), TrustIrBodyVerdict::NotAnswerable(_)),
            "case {mutation}: {report:?}"
        );
        assert!(
            report.function_refusal.is_some(),
            "case {mutation}: {report:?}"
        );
    }
}

#[test]
fn bool_connectives_do_not_admit_bitwise_aliases_or_scalar_not() {
    for op in [BinOp::And, BinOp::Or, BinOp::Xor] {
        let mut fixture = truth_table(BinOp::BAnd, true, false, false);
        let Inst::BinOp { op: selected, .. } =
            &mut fixture.module.functions[0].blocks[0].body[2].inst
        else {
            unreachable!()
        };
        *selected = op;
        let report = run(&fixture);
        assert!(
            matches!(verdict(&report), TrustIrBodyVerdict::NotAnswerable(_)),
            "{report:?}"
        );
    }
    let mut fixture = truth_table(BinOp::BXor, true, true, false);
    fixture.module.functions[0].blocks[0].body[2] = InstrNode::new(Inst::UnOp {
        op: UnOp::Not,
        ty: Ty::Bool,
        operand: ValueId::new(0),
    })
    .with_result(ValueId::new(2));
    let report = run(&fixture);
    assert!(
        matches!(verdict(&report), TrustIrBodyVerdict::NotAnswerable(_)),
        "{report:?}"
    );
}

#[test]
fn bool_native_in_process_answer_remains_advisory_without_artifacts() {
    let fixture = truth_table(BinOp::BXor, false, true, false);
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
        .expect("Bool connective reaches existing advisory entry");
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
