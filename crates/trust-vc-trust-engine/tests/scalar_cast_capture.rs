//! Actual encoder observations do not create a second verification question.
#[path = "support/admission_baseline.rs"]
mod admission_baseline;
use trust_vc_trust_engine::{
    TrustArithOp, TrustCompareOp, TrustExpr, TrustObligation, TrustObligationKind, TrustOutcome,
    TrustSort, TrustVariable, TrustVcTrustEngine, TrustVerificationRequest, TrustVerificationUnit,
    TrustVerifier,
};

fn eq(left: TrustExpr, right: TrustExpr) -> TrustExpr {
    TrustExpr::compare(TrustCompareOp::Eq, left, right)
}
fn variable(name: &str, sort: &TrustSort) -> TrustExpr {
    TrustExpr::variable(name, sort.clone())
}
fn literal(value: i128, sort: &TrustSort) -> TrustExpr {
    TrustExpr::int_literal(value, sort.clone())
}
fn request(unit: TrustVerificationUnit) -> TrustVerificationRequest {
    TrustVerificationRequest::new("actual_cast")
        .with_units(vec![unit])
        .for_full_verification()
}
fn unit() -> TrustVerificationUnit {
    TrustVerificationUnit::new("actual_cast").with_exec_arithmetic()
}
fn assume(unit: TrustVerificationUnit, name: &str, expr: TrustExpr) -> TrustVerificationUnit {
    unit.with_obligation(TrustObligation::assume_typed(
        name,
        TrustObligationKind::Other("body_relation".into()),
        expr,
    ))
}
fn assertion(unit: TrustVerificationUnit, expr: TrustExpr) -> TrustVerificationUnit {
    unit.with_obligation(TrustObligation::ensures_typed("post", expr))
}

#[test]
fn bool_resize_records_actual_raw_names_and_same_native_verdict() {
    let dst = TrustSort::unsigned(16);
    let input = variable("flag$0", &TrustSort::Bool);
    let cast = TrustExpr::cast(input.clone(), TrustSort::Bool, dst.clone());
    let expected = TrustExpr::logic(
        trust_vc_trust_engine::TrustLogicOp::And,
        TrustExpr::implies(input.clone(), eq(cast.clone(), literal(1, &dst))),
        TrustExpr::implies(
            TrustExpr::Not {
                expr: Box::new(input),
            },
            eq(cast, literal(0, &dst)),
        ),
    );
    let request = request(assertion(
        unit().with_variable(TrustVariable::new("flag$0", TrustSort::Bool)),
        expected,
    ));
    let engine = TrustVcTrustEngine::new();
    let native = TrustVerifier::verify(&engine, &request).expect("native request");
    let observed = engine
        .verify_with_scalar_cast_capture(&request)
        .expect("same actual request");
    assert_eq!(
        observed.report().units()[0].outcome(),
        native.units()[0].outcome()
    );
    assert!(matches!(
        native.units()[0].outcome(),
        TrustOutcome::Verified
    ));
    let data = observed.captures()[0]
        .as_ref()
        .expect("bounded Bool cast capture");
    let rows = data
        .conditions()
        .iter()
        .flat_map(|row| &row.casts)
        .collect::<Vec<_>>();
    assert!(!rows.is_empty(), "must observe the actual typed cast");
    eprintln!("ACTUAL_BOOL_CAST_DATA {data:#?}");
    for row in rows {
        assert_eq!(row.operand_variable.as_deref(), Some("flag$0"));
        assert_eq!(row.operand_term, "flag$0");
        assert_eq!(row.operand_sort.to_string(), "Bool");
        assert_eq!(row.result_sort.to_string(), "(_ BitVec 16)");
        assert!(row.result_term.contains("flag$0"), "{}", row.result_term);
        assert!(row.result_term.contains("ite"), "{}", row.result_term);
    }
}

#[test]
fn signed_resize_keeps_actual_sign_extension_and_false_twin() {
    let src = TrustSort::signed(8);
    let dst = TrustSort::signed(16);
    for (claim, verified) in [(-1, true), (255, false)] {
        let x = variable("x", &src);
        let body = unit().with_variable(TrustVariable::new("x", src.clone()));
        let body = assume(body, "input", eq(x.clone(), literal(-1, &src)));
        let request = request(assertion(
            body,
            eq(
                TrustExpr::cast(x, src.clone(), dst.clone()),
                literal(claim, &dst),
            ),
        ));
        let observed = TrustVcTrustEngine::new()
            .verify_with_scalar_cast_capture(&request)
            .expect("real solver");
        assert_eq!(
            matches!(
                observed.report().units()[0].outcome(),
                TrustOutcome::Verified
            ),
            verified
        );
        if !verified {
            assert!(matches!(
                observed.report().units()[0].outcome(),
                TrustOutcome::Refuted { .. }
            ));
        }
        let data = observed.captures()[0].as_ref().expect("signed resize data");
        eprintln!("ACTUAL_SIGNED_CAST_DATA {data:#?}");
        assert!(data.conditions().iter().any(|row| row.phase
            == trust_vc_core::scalar_cast_capture::ScalarCastEncodingPhase::Refutation));
        let casts = data
            .conditions()
            .iter()
            .filter(|row| {
                row.phase
                    == trust_vc_core::scalar_cast_capture::ScalarCastEncodingPhase::CheckedCondition
            })
            .flat_map(|row| &row.casts)
            .collect::<Vec<_>>();
        assert!(!casts.is_empty());
        assert!(
            casts
                .iter()
                .all(|row| row.result_term.contains("sign_extend")),
            "{casts:?}"
        );
    }
}

#[test]
fn cast_operand_division_keeps_final_guarded_domain_inventory() {
    let src = TrustSort::unsigned(8);
    let dst = TrustSort::unsigned(16);
    let x = variable("x", &src);
    let d = variable("divisor", &src);
    let pc = variable("pc$0", &TrustSort::Bool);
    let mut body = unit()
        .with_variable(TrustVariable::new("x", src.clone()))
        .with_variable(TrustVariable::new("divisor", src.clone()))
        .with_variable(TrustVariable::new("pc$0", TrustSort::Bool));
    body = assume(body, "x", eq(x.clone(), literal(4, &src)));
    body = assume(body, "d", eq(d.clone(), literal(2, &src)));
    body = assume(body, "entry", pc.clone());
    let divide = TrustExpr::arith(TrustArithOp::Div, x, d, src.clone());
    let cast = TrustExpr::cast(divide, src, dst.clone());
    let request = request(assertion(
        body,
        TrustExpr::implies(pc, eq(cast, literal(2, &dst))),
    ));
    let observed = TrustVcTrustEngine::new()
        .verify_with_scalar_cast_capture(&request)
        .expect("real domain check");
    assert!(
        matches!(
            observed.report().units()[0].outcome(),
            TrustOutcome::Verified
        ),
        "{:?}",
        observed.report()
    );
    let data = observed.captures()[0].as_ref().expect("domain inventory");
    eprintln!("ACTUAL_DOMAIN_DATA {data:#?}");
    let row = data
        .conditions()
        .iter()
        .find(|row| !row.casts.is_empty())
        .expect("cast root");
    assert!(
        !row.domain_checks.is_empty(),
        "division domain must not disappear"
    );
    assert!(
        row.domain_checks
            .iter()
            .any(|check| check.predicate.contains("divisor") && check.predicate.contains("pc$0")),
        "{:?}",
        row.domain_checks
    );
    assert_eq!(row.casts[0].operand_variable, None);
    assert!(
        row.casts[0].operand_term.contains("bvudiv"),
        "{:?}",
        row.casts[0]
    );
}

#[test]
fn observation_bound_refuses_data_without_changing_native_coverage() {
    let name = "x".repeat(5000);
    let sort = TrustSort::unsigned(8);
    let x = variable(&name, &sort);
    let body = unit().with_variable(TrustVariable::new(&name, sort.clone()));
    let expr = eq(
        TrustExpr::cast(x, sort, TrustSort::unsigned(16)),
        literal(0, &TrustSort::unsigned(16)),
    );
    let request = request(assertion(body, expr));
    let engine = TrustVcTrustEngine::new();
    let native = TrustVerifier::verify(&engine, &request).expect("native request");
    let observed = engine
        .verify_with_scalar_cast_capture(&request)
        .expect("observation does not refuse native execution");
    assert_eq!(
        native.units()[0].outcome(),
        observed.report().units()[0].outcome()
    );
    assert!(
        observed.captures()[0].is_err(),
        "oversized lexical input must not produce a mathematical binding"
    );
}

#[cfg(feature = "proof-certificates")]
fn native_bundle() -> trust_ir::request::NativeVerificationBundle {
    use trust_ir::inst::CastOp;
    use trust_ir::request::{
        NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeObligationCause,
        NativeObligationSource, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
        NativeVerificationBundle, NativeVerificationRequest, TrustVcNativeRequest,
        TrustVcVerificationMode,
    };
    use trust_ir::{
        BlockId, FuncId, ObligationKind, ObligationSite, ProofFormula, ProofId,
        ProofLineageManifest, ProofObligation, ProofObligationSourceIdentity, ProofReplayIdentity,
        ProofStatus, ProofTransform, ProofTransformStage, PublicObligationIdentity, Ty,
    };
    let mut builder = trust_ir_build::ModuleBuilder::new("actual_scalar_cast");
    let ty = builder.add_func_type(vec![], vec![Ty::U16]);
    let mut function = builder.function("actual_scalar_cast", ty);
    let entry = function.create_block();
    function.switch_to_block(entry);
    function.set_entry(entry);
    let input = function.bool_const(true);
    let cast = function.cast(CastOp::ZExt, Ty::Bool, Ty::U16, input);
    function.ret(vec![cast]);
    function.build();
    let mut module = builder.build().expect("canonical original module");
    let public_id = "vc:synthetic_scalar_cast:postcondition:0";
    module.proof_obligations.push(ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Pending,
        description: "synthetic native cast result, not Rust source authority".into(),
        formula: Some(ProofFormula::new(
            "trust-types.Formula@1",
            serde_json::json!({"formula":{"Eq":[{"Var":["_0","Int"]},{"Int":1}]},
                "source":{"assertion_id":"rust-assertion:1","native_assertion_id":1}})
            .to_string(),
        )),
        function: Some(FuncId::new(0)),
        source: Some(
            ProofObligationSourceIdentity::new("synthetic:scalar-cast", "rust-assertion:1")
                .with_public(PublicObligationIdentity {
                    obligation_id: public_id.into(),
                    semantic_digest: trust_ir::ProofDigest::sha256([0x52; 32]),
                }),
        ),
        site: Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 2)),
        spec: None,
    });
    // A synthetic native INPUT recipe is ordinary producer data. No certificate,
    // proof transcript, Rust source generation, or Source/ABI grade is supplied.
    // The only proof in this test is produced below by the actual native verifier.
    let digest = module.stable_digest();
    use sha2::Digest as _;
    let construction_bytes = trust_ir::binary::serialize_module(&module).unwrap();
    let construction_digest =
        trust_ir::ProofDigest::sha256(sha2::Sha256::digest(&construction_bytes).into());
    let replay = ProofReplayIdentity::new(
        "trust_vc",
        "synthetic-native-question module-wire construction",
    )
    .with_transcript_digest(construction_digest);
    let mut lineage = ProofLineageManifest::new();
    let root = lineage
        .append_pass(
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "synthetic native question",
                "test data",
                "1",
            ),
            digest,
            digest,
            vec![ProofId::new(0)],
            vec![],
        )
        .expect("normal canonical lineage constructor");
    lineage.nodes[0].replay = Some(replay.clone());
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        digest,
        module,
        lineage,
    );
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: public_id.into(),
            function: Some(FuncId::new(0)),
            span: Some(trust_ir::SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(1)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: vec![],
        });
    let provenance = NativeRequestProvenance::trust_vc(NativeToolIdentity::new("trust_vc"))
        .with_solver(NativeToolIdentity::new("ay"))
        .with_replay(replay)
        .with_replay_context(admission_baseline::bridge_replay_context(
            &bundle.module,
            &bundle.compiler_facts,
            &[ProofId::new(0)],
        ));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustVcVerificationMode::DischargeProofObligations,
            obligations: vec![ProofId::new(0)],
            certificates: Vec::new(),
            lineage_roots: vec![root],
            options: Default::default(),
            diagnostics: Default::default(),
            provenance,
            function: Some(FuncId::new(0)),
        }));
    assert!(bundle.module.proof_certificates.is_empty());
    assert!(bundle.evidence_bundles.is_empty());
    bundle
}

#[test]
#[cfg(feature = "proof-certificates")]
fn original_native_cast_binding_covers_full_input_artifact_and_domain_changes() {
    use trust_ir::inst::{BinOp, CastOp, Inst};
    use trust_ir::interpret::Interpreter;
    use trust_ir::{Constant, FuncId, InstrNode, Ty, ValueId};
    let bundle = native_bundle();
    let before = serde_json::to_vec(&bundle).unwrap();
    let canonical = Interpreter::with_module(&bundle.module)
        .execute_func(FuncId::new(0), [])
        .expect("canonical Bool ZExt");
    assert_eq!(canonical.returns[0].as_int().unwrap().raw, 1);
    let observed = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle_with_scalar_cast_bindings(&bundle)
        .expect("actual native discharge");
    assert_eq!(
        observed.report().produced_certificates().len(),
        1,
        "{:?}",
        observed.report()
    );
    assert_eq!(observed.bindings().len(), 1, "{:?}", observed.bindings());
    let binding = observed.bindings()[0]
        .as_ref()
        .expect("same actual emission binding");
    eprintln!("ACTUAL_ORIGINAL_NATIVE_CAST_DATA {:#?}", binding.encoding());
    let certificate = &observed.report().produced_certificates()[0];
    assert!(certificate.kernel_verified() && certificate.strict_verified());
    assert!(binding.matches(&bundle, certificate));
    assert_eq!(
        binding.original_module_bytes(),
        trust_ir::binary::serialize_module(&bundle.module).unwrap()
    );
    assert_eq!(binding.original_bundle_bytes(), before);
    assert_eq!(binding.sites().len(), 1);
    assert_eq!(binding.sites()[0].opcode, CastOp::ZExt);
    assert_eq!(binding.sites()[0].function, 0);
    assert!(!binding.encoding().conditions().is_empty());
    assert_eq!(
        serde_json::to_vec(&bundle).unwrap(),
        before,
        "original input is immutable"
    );

    let mut changed = bundle.clone();
    let Inst::Cast { op, .. } = &mut changed.module.functions[0].blocks[0].body[1].inst else {
        panic!("cast site")
    };
    *op = CastOp::SExt;
    changed.trust_ir_module_digest = changed.module.stable_digest();
    let canonical = Interpreter::with_module(&changed.module)
        .execute_func(FuncId::new(0), [])
        .expect("canonical Bool SExt");
    assert_eq!(canonical.returns[0].as_int().unwrap().raw, u16::MAX as u128);
    assert!(
        !binding.matches(&changed, certificate),
        "a different actual cast cannot reuse this binding"
    );

    let mut changed = bundle.clone();
    // An additional domain-sensitive operation is part of the original module
    // even if its value is unused. Rehashing the producer identity cannot hide it.
    let body = &mut changed.module.functions[0].blocks[0].body;
    body.insert(
        2,
        InstrNode::new(Inst::Const {
            ty: Ty::U16,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(3)),
    );
    body.insert(
        3,
        InstrNode::new(Inst::BinOp {
            op: BinOp::UDiv,
            ty: Ty::U16,
            lhs: ValueId::new(1),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    changed.module.proof_obligations[0]
        .site
        .as_mut()
        .unwrap()
        .inst_index = 4;
    let error = Interpreter::with_module(&changed.module)
        .execute_func(FuncId::new(0), [])
        .expect_err("the original divisor domain is false");
    assert_eq!(
        error.code,
        trust_ir::interpret::InterpretErrorCode::UndefinedBehavior
    );
    assert!(
        error.message.contains("unsigned division by zero"),
        "{error:?}"
    );
    changed.trust_ir_module_digest = changed.module.stable_digest();
    assert!(!binding.matches(&changed, certificate));

    let mut changed = bundle.clone();
    changed.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .payload = "{\"formula\":{\"Bool\":false}}".into();
    changed.trust_ir_module_digest = changed.module.stable_digest();
    assert!(
        !binding.matches(&changed, certificate),
        "full original contract bytes stay bound"
    );

    let mut changed = bundle.clone();
    changed.module.proof_obligations[0]
        .description
        .push_str(" different original identity");
    changed.trust_ir_module_digest = changed.module.stable_digest();
    assert!(
        !binding.matches(&changed, certificate),
        "full metadata stays bound independently of semantic hashes"
    );

    let mut changed_certificate = serde_json::to_value(certificate).unwrap();
    changed_certificate["alethe"] =
        serde_json::Value::String("not the original native proof".into());
    let changed_certificate = serde_json::from_value(changed_certificate).unwrap();
    assert!(!binding.matches(&bundle, &changed_certificate));
}
