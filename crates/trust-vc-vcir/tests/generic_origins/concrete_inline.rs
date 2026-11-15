//! Concrete trait dispatch keeps each inline instance's independent value.

use super::*;

fn function(n: u64, result: Ty) -> FnDecl {
    let mut declaration = original();
    declaration.id = id(n);
    declaration.name = format!("declaration{n}");
    declaration.type_params.clear();
    declaration.locals = vec![local(result, LocalKind::Return)];
    declaration.params.clear();
    declaration
}

fn call(n: u64, type_args: Vec<Ty>) -> Expr {
    Expr::new(
        Ty::uint(32),
        SpanId(0),
        ExprKind::Call {
            callee: id(n),
            type_args,
            args: vec![],
        },
    )
}

fn fixture(condition: Expr, isolated: bool) -> VcCrate {
    let mut required = function(10, Ty::uint(32));
    required.role = FnRole::TraitDecl;
    required.kind = FnKind::Constant(ConstMode::Dual);
    required.type_params = vec!["Self".into()];
    required.locals[0].mode = Mode::Exec;
    let mut generic = function(1, Ty::uint(32));
    generic.type_params = vec!["A".into()];
    generic.attrs.inline = true;
    generic.body = Body::Spec(call(10, vec![Ty::Param(0)]));
    let mut functions = vec![generic.clone(), required];
    for (n, constant_id, argument, value) in [(2, 11, Ty::Bool, 3), (3, 12, Ty::uint(8), 5)] {
        let mut constant = function(constant_id, Ty::uint(32));
        constant.kind = FnKind::Constant(ConstMode::Dual);
        constant.locals[0].mode = Mode::Exec;
        constant.body = Body::Constant(Expr::int_lit(value, Ty::uint(32), SpanId(0)));
        let mut instance = generic.clone();
        instance.id = id(n);
        instance.name = "same_selected_name".into();
        instance.role = FnRole::Instance;
        instance.type_params.clear();
        instance.attrs.instance = Some(GenericInstance {
            declaration: generic.id,
            type_args: vec![argument],
        });
        instance.body = Body::Spec(call(constant_id, vec![]));
        functions.extend([constant, instance]);
    }
    let mut proof = function(99, Ty::Unit);
    proof.mode = Mode::Proof;
    let assertion = if isolated {
        StmtKind::AssertBitVector {
            requires: vec![],
            ensures: vec![Clause {
                span: SpanId(0),
                expr: condition,
                attrs: ClauseAttrs::default(),
            }],
            architecture: bitvector::Architecture::Either32Or64,
            site: SiteId(0),
        }
    } else {
        StmtKind::Assert {
            expr: condition,
            site: SiteId(0),
            attrs: ClauseAttrs::default(),
        }
    };
    proof.body = Body::Stmts(Block::new(vec![
        Stmt {
            span: SpanId(0),
            kind: assertion,
        },
        Stmt {
            span: SpanId(0),
            kind: StmtKind::Return {
                value: None,
                site: SiteId(1),
            },
        },
    ]));
    functions.push(proof);
    let mut source = VcCrate::new("independent concrete inline bodies");
    source.architecture = bitvector::Architecture::Either32Or64;
    source.fns = functions;
    source
}

fn sum_is(expected: i128) -> Expr {
    let value = |n| call(n, vec![]).cast(CastKind::Exact, Ty::int(), SpanId(0));
    Expr::binary(
        BinOp::Eq,
        Expr::binary(BinOp::Add, value(2), value(3), Ty::int(), SpanId(0)),
        Expr::int_lit(expected, Ty::int(), SpanId(0)),
        Ty::Bool,
        SpanId(0),
    )
}

fn answer(source: &VcCrate, proved: bool) {
    assert!(check_crate(source).is_empty(), "{:?}", check_crate(source));
    let generated = vcgen::generate(source);
    let Some(vcgen::FnVcs::Checks(checks)) = generated.get(id(99)) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 1);
    #[cfg(feature = "solve")]
    {
        let result = solve::check(
            &checks[0].query,
            "independent inline body",
            &solve::Limits::default(),
        );
        assert!(
            if proved {
                matches!(result, solve::Verdict::Proved { .. })
            } else {
                matches!(result, solve::Verdict::Refuted { .. })
            },
            "{result:?}"
        );
    }
    #[cfg(not(feature = "solve"))]
    let _ = proved;
}

#[test]
fn native_selected_values_inline_without_collapsing_the_two_dispatches() {
    for isolated in [false, true] {
        answer(&fixture(sum_is(8), isolated), true);
        answer(&fixture(sum_is(9), isolated), false);
    }
}

#[test]
fn independent_inline_body_does_not_define_the_generic_uf() {
    let condition = Expr::binary(
        BinOp::Eq,
        call(1, vec![Ty::Bool]),
        call(2, vec![]),
        Ty::Bool,
        SpanId(0),
    );
    answer(&fixture(condition, false), false);
}

#[test]
fn changed_instance_origins_modes_attributes_and_signatures_remain_malformed() {
    for mutation in 0..5 {
        let mut source = fixture(sum_is(8), false);
        let instance = source.fns.iter_mut().find(|decl| decl.id == id(2)).unwrap();
        match mutation {
            0 => instance.attrs.instance.as_mut().unwrap().declaration = id(404),
            1 => instance.attrs.instance.as_mut().unwrap().type_args = vec![Ty::Param(0)],
            2 => instance.mode = Mode::Proof,
            3 => instance.attrs.opaque = true,
            _ => instance.locals[0].ty = Ty::uint(64),
        }
        assert!(
            check_crate(&source)
                .iter()
                .any(|error| error.class == WfClass::Malformed && error.function == Some(id(2))),
            "mutation={mutation}"
        );
    }
}

#[test]
fn missing_opaque_imported_or_recursive_origins_cannot_supply_inline_values() {
    for mutation in 0..4 {
        let mut source = fixture(sum_is(8), false);
        match mutation {
            0 => {
                source
                    .fns
                    .iter_mut()
                    .find(|decl| decl.id == id(2))
                    .unwrap()
                    .attrs
                    .instance = None
            }
            1 => {
                for decl in &mut source.fns {
                    if [id(1), id(2), id(3)].contains(&decl.id) {
                        decl.attrs.opaque = true;
                    }
                }
            }
            2 => source.fns[0].role = FnRole::Imported,
            _ => source.rec_groups.push(RecGroup {
                members: vec![(id(1), 1)],
            }),
        }
        let generated = vcgen::generate(&source);
        assert!(
            matches!(generated.get(id(99)), Some(vcgen::FnVcs::Refused(_))),
            "mutation={mutation}: {generated:?}"
        );
    }
}
