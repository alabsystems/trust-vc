use super::*;

fn equality_source(ty: Ty, scalar_inputs: bool) -> VcCrate {
    let goal = binary(
        BinOp::Eq,
        read(1, ty.clone()),
        read(2, ty.clone()),
        Ty::Bool,
    );
    let mut function = proof(ty, vec![isolated(goal, vec![], Architecture::Exactly(64))]);
    let mut second = function.locals[1].clone();
    second.name = "y".into();
    function.locals.push(second);
    function.params.push(LocalId(2));
    function.attrs.bitvector_scalar_inputs = scalar_inputs;
    let mut krate = source(Architecture::Exactly(64), function);
    krate.adts.push(AdtDecl {
        id: AdtId(DefHash::new(81, 2)),
        name: "test_crate::X".into(),
        type_params: vec![],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "X".into(),
            fields: vec![],
        }],
    });
    krate
}

#[test]
fn source_scalar_fragment_rejects_products_without_removing_ir_product_support() {
    for ty in [
        Ty::Unit,
        Ty::Tuple(vec![Ty::Unit]),
        Ty::Adt(AdtId(DefHash::new(81, 2)), vec![]),
    ] {
        let rich = equality_source(ty, false);
        let generated = checks(&rich);
        let query = &generated[0].query.bitvector.as_ref().unwrap()[0];
        assert!(query.variables.is_empty());
        assert!(query.validate().is_ok());
        #[cfg(feature = "solve")]
        assert!(matches!(
            trust_vc_vcir::solve::check(
                &generated[0].query,
                "finite singleton product",
                &trust_vc_vcir::solve::Limits::default()
            ),
            trust_vc_vcir::solve::Verdict::Proved { .. }
        ));

        let mut scalar = rich.clone();
        scalar.fns[0].attrs.bitvector_scalar_inputs = true;
        let expected = format!(
            "bit_vector prover cannot handle type `{}`",
            trust_vc_vcir::pretty::ty_name(&scalar, &scalar.fns[0].locals[1].ty)
        );
        let generated = vcgen::generate(&scalar);
        let FnVcs::Refused(problem) = generated.get(scalar.fns[0].id).unwrap() else {
            panic!("a source product input was admitted: {generated:?}")
        };
        assert_eq!(problem.tag, "bit-vector-type");
        assert_eq!(problem.detail, expected);
    }
}

#[cfg(feature = "solve")]
#[test]
fn source_scalar_fragment_keeps_true_and_false_scalar_queries() {
    use trust_vc_vcir::solve::{self, Limits, Verdict};
    for ty in [Ty::Bool, Ty::uint(8)] {
        for equal in [false, true] {
            let mut krate = equality_source(ty.clone(), true);
            if equal {
                let Body::Stmts(block) = &mut krate.fns[0].body else {
                    unreachable!()
                };
                block.stmts[0] = isolated(
                    binary(
                        BinOp::Eq,
                        read(1, ty.clone()),
                        read(1, ty.clone()),
                        Ty::Bool,
                    ),
                    vec![],
                    Architecture::Exactly(64),
                );
            }
            let generated = checks(&krate);
            let verdict = solve::check(
                &generated[0].query,
                "source scalar inputs",
                &Limits::default(),
            );
            if equal {
                assert!(matches!(verdict, Verdict::Proved { .. }), "{verdict:?}");
            } else {
                assert!(matches!(verdict, Verdict::Refuted { .. }), "{verdict:?}");
            }
        }
    }
}

#[test]
fn source_product_restriction_follows_retained_sst_queries() {
    let original = equality_source(Ty::Adt(AdtId(DefHash::new(81, 2)), vec![]), true);
    let mut pruned = original.clone();
    let Body::Stmts(block) = &mut pruned.fns[0].body else {
        unreachable!()
    };
    block.stmts.insert(
        0,
        Stmt::new(
            SpanId(0),
            StmtKind::Return {
                value: None,
                site: SiteId(1),
            },
        ),
    );
    assert!(checks(&pruned).is_empty());

    let mut dead_branch = original;
    let Body::Stmts(block) = &mut dead_branch.fns[0].body else {
        unreachable!()
    };
    block.stmts[0] = bv_if(
        Expr::bool_lit(false, SpanId(0)),
        vec![block.stmts[0].clone()],
        vec![],
    );
    assert!(check_crate(&dead_branch).is_empty());
    let generated = vcgen::generate(&dead_branch);
    let FnVcs::Refused(problem) = generated.get(dead_branch.fns[0].id).unwrap() else {
        panic!("an ordinary dead branch lost its source query: {generated:?}")
    };
    assert_eq!(problem.tag, "bit-vector-type");
}
