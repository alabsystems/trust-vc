// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use trust_ir::{
    Block, BlockId, ClosureTy, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Ty, ValueId,
};
use trust_vc_trust_engine::{
    LoweringWitness, TrustIrBodyAuthority, TrustIrBodyOptions, TrustIrBodyRefusal,
    TrustIrBodyVerdict, TrustVcTrustEngine,
};

fn fixture(construct: bool) -> fixtures::Fixture {
    let mut fixture = fixtures::expected_true_shape();
    let apparent = fixture
        .module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let physical = fixture
        .module
        .add_func_type(FuncTy {
            params: vec![Ty::U8; 3],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let closure = fixture
        .module
        .add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::U8; 3],
        })
        .unwrap();
    let mut target = Function::new(FuncId::new(1), "target", physical, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = (0..3).map(|id| (ValueId::new(id), Ty::U8)).collect();
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    target.blocks.push(block);
    fixture.module.try_add_function(target).unwrap();
    if construct {
        fixture.module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::MakeClosure {
                ty: closure,
                func: FuncId::new(1),
                captures: vec![ValueId::new(0); 3],
            })
            .with_result(ValueId::new(99)),
        );
        for obligation in &mut fixture.module.proof_obligations {
            obligation.site.as_mut().unwrap().inst_index += 1;
        }
    }
    fixture
}

#[test]
fn unused_runtime_closure_is_a_named_whole_body_refusal() {
    let fixture = fixture(true);
    assert!(trust_ir_build::validate_module(&fixture.module).is_empty());
    let execution = trust_ir::interpret::Interpreter::with_module(&fixture.module)
        .execute_func(
            fixture.function(),
            [trust_ir::interpret::InterpretValue::int(Ty::U8, 3).unwrap()],
        )
        .unwrap();
    assert!(execution.returns.is_empty());
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions::default(),
        )
        .unwrap();
    assert!(matches!(
        report.function_refusal.as_ref(),
        Some(TrustIrBodyRefusal::UnsupportedInstruction {
            block,
            inst_index: 0,
            inst: "MakeClosure",
            detail,
        }) if *block == BlockId::new(0) && detail.contains("ordered live captures")
    ));
    assert_eq!(report.obligations.len(), 1);
    assert!(matches!(
        &report.obligations[0].verdict,
        TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::UnsupportedInstruction {
            inst: "MakeClosure",
            ..
        })
    ));
    assert_eq!(report.authority, TrustIrBodyAuthority::Advisory);
    assert_eq!(report.lowering_witness, LoweringWitness::None);
}

#[test]
fn scalar_twin_keeps_advisory_discharge_and_refutes_the_changed_bound() {
    let mut fixture = fixture(false);
    let engine = TrustVcTrustEngine::new();
    for (bound, should_discharge) in [(16, true), (0, false)] {
        let value = fixture.module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find_map(|node| match &mut node.inst {
                Inst::Const {
                    value: Constant::Int(value),
                    ..
                } if *value == 16 => Some(value),
                _ => None,
            })
            .expect("the scalar assertion's bound is 16 before mutation");
        *value = bound;
        assert!(trust_ir_build::validate_module(&fixture.module).is_empty());
        let report = engine
            .discharge_trust_ir_function(
                &fixture.module,
                fixture.function(),
                &TrustIrBodyOptions::default(),
            )
            .unwrap();
        assert!(report.function_refusal.is_none());
        assert_eq!(report.obligations.len(), 1);
        if should_discharge {
            assert!(report.obligations[0].verdict.is_discharged_advisory());
        } else {
            assert!(matches!(
                report.obligations[0].verdict,
                TrustIrBodyVerdict::Refuted { .. }
            ));
        }
        assert_eq!(report.authority, TrustIrBodyAuthority::Advisory);
        assert_eq!(report.lowering_witness, LoweringWitness::None);
    }
}
