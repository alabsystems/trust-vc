//! Program-level BV isolation, complete ordinary architectures and source ABI.
//! Prepared controls; no claimed runtime qualification accompanies this file.

use trust_vc_vcir::bitvector::{Architecture, Sort as BvSort};
use trust_vc_vcir::vcgen::{self, Check, CheckKind, FnVcs};
use trust_vc_vcir::*;

fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}
fn integer(value: u128) -> Expr {
    Expr::new(
        Ty::nat(),
        SpanId(0),
        ExprKind::Lit(Lit::Int(IntLit {
            negative: false,
            magnitude: value,
        })),
    )
}
fn binary(op: BinOp, left: Expr, right: Expr, ty: Ty) -> Expr {
    Expr::binary(op, left, right, ty, SpanId(0))
}
fn clause(expr: Expr) -> Clause {
    Clause {
        expr,
        span: SpanId(0),
        attrs: ClauseAttrs::default(),
    }
}
fn proof(ty: Ty, mut statements: Vec<Stmt>) -> FnDecl {
    statements.push(Stmt::new(
        SpanId(0),
        StmtKind::Return {
            value: None,
            site: SiteId(2),
        },
    ));
    FnDecl {
        id: FnId(DefHash::new(81, 1)),
        name: "test".into(),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![
            LocalDecl {
                name: "ret".into(),
                ty: Ty::Unit,
                mode: Mode::Spec,
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(0),
            },
            LocalDecl {
                name: "x".into(),
                ty,
                mode: Mode::Spec,
                mutable: false,
                kind: LocalKind::Param,
                span: SpanId(0),
            },
        ],
        params: vec![LocalId(1)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::new(statements)),
    }
}
fn isolated(goal: Expr, requires: Vec<Clause>, architecture: Architecture) -> Stmt {
    Stmt::new(
        SpanId(0),
        StmtKind::AssertBitVector {
            requires,
            ensures: vec![clause(goal)],
            architecture,
            site: SiteId(0),
        },
    )
}
fn assertion(goal: Expr, site: u32) -> Stmt {
    Stmt::new(
        SpanId(0),
        StmtKind::Assert {
            expr: goal,
            site: SiteId(site),
            attrs: ClauseAttrs::default(),
        },
    )
}
fn source(architecture: Architecture, function: FnDecl) -> VcCrate {
    let mut krate = VcCrate::new("isolated BV source control");
    krate.architecture = architecture;
    krate.fns.push(function);
    krate
}
fn checks(krate: &VcCrate) -> Vec<Check> {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let generated = vcgen::generate(krate);
    let FnVcs::Checks(checks) = generated.get(krate.fns[0].id).unwrap() else {
        panic!("{generated:?}")
    };
    checks.clone()
}

#[test]
fn surrounding_requires_and_source_value_bindings_are_not_bv_hypotheses() {
    let ty = Ty::Int(IntRange::U(8));
    let goal = binary(
        BinOp::Eq,
        read(1, ty.clone()),
        Expr::int_lit(3, ty.clone(), SpanId(0)),
        Ty::Bool,
    );
    let mut statement = isolated(goal.clone(), vec![], Architecture::Exactly(64));
    statement.span = SpanId(9);
    let mut function = proof(ty, vec![statement]);
    function.requires.push(clause(goal));
    let generated = checks(&source(Architecture::Exactly(64), function));
    assert_eq!(generated.len(), 1);
    assert!(matches!(
        generated[0].kind,
        CheckKind::BitvectorAssert {
            span: SpanId(9),
            ..
        }
    ));
    let query = &generated[0].query;
    assert!(query.architectures.is_none());
    assert!(query.hypotheses.is_empty() && query.functions.is_empty() && query.symbols.is_empty());
    let cases = query.bitvector.as_ref().unwrap();
    assert_eq!(cases.len(), 1);
    assert!(cases[0].requires.is_empty());
    assert_eq!(cases[0].variables.len(), 1);
    assert_eq!(cases[0].variables[0].1, BvSort::Bits(8));
}

#[test]
fn explicit_bv_requirements_have_separate_outer_checks_and_inner_premises() {
    let ty = Ty::Int(IntRange::U(16));
    let premise = binary(
        BinOp::Eq,
        read(1, ty.clone()),
        Expr::int_lit(3, ty.clone(), SpanId(0)),
        Ty::Bool,
    );
    let goal = binary(
        BinOp::Eq,
        binary(
            BinOp::BitAnd,
            read(1, ty.clone()),
            Expr::int_lit(1, ty.clone(), SpanId(0)),
            ty.clone(),
        ),
        Expr::int_lit(1, ty.clone(), SpanId(0)),
        Ty::Bool,
    );
    let generated = checks(&source(
        Architecture::Exactly(64),
        proof(
            ty,
            vec![isolated(
                goal,
                vec![clause(premise)],
                Architecture::Exactly(64),
            )],
        ),
    ));
    assert_eq!(generated.len(), 2);
    assert!(matches!(
        generated[0].kind,
        CheckKind::BitvectorRequires { .. }
    ));
    assert!(generated[0].query.bitvector.is_none());
    assert_eq!(
        generated[1].query.bitvector.as_ref().unwrap()[0]
            .requires
            .len(),
        1
    );
}

#[test]
fn ordinary_continuation_keeps_the_boxed_uf_abi_and_no_native_bv_law() {
    use vcgen::term::Sort;
    let ty = Ty::Int(IntRange::U(8));
    let goal = binary(
        BinOp::Eq,
        binary(
            BinOp::BitAnd,
            read(1, ty.clone()),
            read(1, ty.clone()),
            ty.clone(),
        ),
        read(1, ty.clone()),
        Ty::Bool,
    );
    let generated = checks(&source(
        Architecture::Exactly(64),
        proof(
            ty,
            vec![
                isolated(goal.clone(), vec![], Architecture::Exactly(64)),
                assertion(goal, 1),
            ],
        ),
    ));
    assert_eq!(generated.len(), 2);
    assert!(matches!(
        generated[0].kind,
        CheckKind::BitvectorAssert { .. }
    ));
    assert!(matches!(generated[1].kind, CheckKind::Assert { .. }));
    let ordinary = &generated[1].query;
    assert!(ordinary.bitvector.is_none() && ordinary.architectures.is_none());
    let function = ordinary
        .functions
        .iter()
        .find(|function| function.name == "bit_and")
        .unwrap();
    assert_eq!(function.params, vec![Sort::Poly, Sort::Poly]);
    assert_eq!(function.ret, Sort::Int);
    assert!(ordinary
        .hypotheses
        .iter()
        .any(|fact| fact.source == vcgen::Source::Assert));
    assert!(ordinary
        .functions
        .iter()
        .all(|function| !function.name.starts_with("bv_")));
}

#[test]
fn pointer_width_proofs_are_one_source_site_over_two_complete_contexts() {
    let ty = Ty::Int(IntRange::USize);
    let goal = binary(
        BinOp::Eq,
        binary(
            BinOp::BitXor,
            read(1, ty.clone()),
            read(1, ty.clone()),
            ty.clone(),
        ),
        Expr::int_lit(0, ty.clone(), SpanId(0)),
        Ty::Bool,
    );
    let generated = checks(&source(
        Architecture::Either32Or64,
        proof(ty, vec![isolated(goal, vec![], Architecture::Either32Or64)]),
    ));
    assert_eq!(
        generated.len(),
        1,
        "one actual source obligation, not two scored assertions"
    );
    assert!(matches!(
        generated[0].kind,
        CheckKind::BitvectorAssert { .. }
    ));
    let cases = generated[0].query.architectures.as_ref().unwrap();
    assert_eq!(
        cases.iter().map(|(width, _)| *width).collect::<Vec<_>>(),
        [32, 64]
    );
    for (width, query) in cases {
        let isolated = query.bitvector.as_ref().unwrap();
        assert_eq!(isolated.len(), 1);
        assert_eq!(isolated[0].architecture, *width);
        assert_eq!(isolated[0].variables[0].1, BvSort::Bits(*width));
    }
}

#[test]
fn an_isolated_assertion_cannot_silently_choose_a_different_architecture() {
    let krate = source(
        Architecture::Either32Or64,
        proof(
            Ty::Bool,
            vec![isolated(
                Expr::bool_lit(true, SpanId(0)),
                vec![],
                Architecture::Exactly(64),
            )],
        ),
    );
    assert!(!check_crate(&krate).is_empty());
}

#[cfg(feature = "solve")]
#[test]
fn ordinary_pointer_bounds_are_checked_for_both_architectures() {
    use trust_vc_vcir::solve::{self, Limits, Verdict};
    for (limit, valid) in [(u32::MAX as u128, false), (u64::MAX as u128, true)] {
        let ty = Ty::Int(IntRange::USize);
        let goal = binary(
            BinOp::Le,
            read(1, ty.clone()).cast(CastKind::Exact, Ty::nat(), SpanId(0)),
            integer(limit),
            Ty::Bool,
        );
        let generated = checks(&source(
            Architecture::Either32Or64,
            proof(ty, vec![assertion(goal, 0)]),
        ));
        assert_eq!(generated.len(), 1);
        let result = solve::check(
            &generated[0].query,
            "ordinary complete pointer bounds",
            &Limits::default(),
        );
        if valid {
            assert!(matches!(result, Verdict::Proved { .. }), "{result:?}");
        } else {
            assert!(matches!(result, Verdict::Refuted { .. }), "{result:?}");
        }
    }
}

#[cfg(feature = "solve")]
#[test]
fn u128_bounds_do_not_drop_the_upper_half_of_the_domain() {
    use trust_vc_vcir::solve::{self, Limits, Verdict};
    for (limit, valid) in [(i128::MAX as u128, false), (u128::MAX, true)] {
        let ty = Ty::Int(IntRange::U(128));
        let goal = binary(
            BinOp::Le,
            read(1, ty.clone()).cast(CastKind::Exact, Ty::nat(), SpanId(0)),
            integer(limit),
            Ty::Bool,
        );
        let generated = checks(&source(
            Architecture::Exactly(64),
            proof(ty, vec![assertion(goal, 0)]),
        ));
        let result = solve::check(
            &generated[0].query,
            "full u128 mathematical bounds",
            &Limits::default(),
        );
        if valid {
            assert!(matches!(result, Verdict::Proved { .. }), "{result:?}");
        } else {
            assert!(matches!(result, Verdict::Refuted { .. }), "{result:?}");
        }
    }
}

#[test]
fn actual_default_width_consumption_is_shared_by_all_sibling_ensures() {
    let width = Expr::new(
        Ty::Int(IntRange::U(32)),
        SpanId(0),
        ExprKind::IntegerConstant(IntegerConstant::WordBits),
    );
    let consumes = binary(
        BinOp::Eq,
        width,
        Expr::int_lit(32, Ty::Int(IntRange::U(32)), SpanId(0)),
        Ty::Bool,
    );
    let statement = Stmt::new(
        SpanId(9),
        StmtKind::AssertBitVector {
            requires: vec![],
            ensures: vec![clause(Expr::bool_lit(false, SpanId(0))), clause(consumes)],
            architecture: Architecture::Either32Or64,
            site: SiteId(0),
        },
    );
    let generated = checks(&source(
        Architecture::Either32Or64,
        proof(Ty::Int(IntRange::USize), vec![statement]),
    ));
    assert_eq!(generated.len(), 2);
    for check in &generated {
        assert!(matches!(
            &check.kind,
            CheckKind::BitvectorAssert {
                span: SpanId(9),
                architecture_specialized: true
            }
        ));
        assert_eq!(check.query.architectures.as_ref().unwrap().len(), 2);
    }
    assert_eq!(generated[0].group, generated[1].group);
    assert_eq!(generated[0].site, generated[1].site);
}

#[test]
fn fixed_width_and_unused_pointer_parameter_do_not_claim_specialization() {
    for architecture in [
        Architecture::Either32Or64,
        Architecture::Exactly(32),
        Architecture::Exactly(64),
    ] {
        let generated = checks(&source(
            architecture,
            proof(
                Ty::Int(IntRange::USize),
                vec![isolated(
                    Expr::bool_lit(false, SpanId(0)),
                    vec![],
                    architecture,
                )],
            ),
        ));
        assert_eq!(generated.len(), 1);
        assert!(matches!(
            &generated[0].kind,
            CheckKind::BitvectorAssert {
                architecture_specialized: false,
                ..
            }
        ));
    }
}

#[test]
fn pointer_requirements_share_specialization_but_remain_outer_mathematical_checks() {
    let width = Expr::new(
        Ty::Int(IntRange::U(32)),
        SpanId(0),
        ExprKind::IntegerConstant(IntegerConstant::WordBits),
    );
    let consumes = binary(
        BinOp::Eq,
        width,
        Expr::int_lit(32, Ty::Int(IntRange::U(32)), SpanId(0)),
        Ty::Bool,
    );
    let generated = checks(&source(
        Architecture::Either32Or64,
        proof(
            Ty::Int(IntRange::U(8)),
            vec![isolated(
                Expr::bool_lit(false, SpanId(0)),
                vec![clause(consumes)],
                Architecture::Either32Or64,
            )],
        ),
    ));
    assert_eq!(generated.len(), 2);
    assert!(matches!(
        &generated[0].kind,
        CheckKind::BitvectorRequires { .. }
    ));
    assert!(generated[0]
        .query
        .architectures
        .as_ref()
        .unwrap()
        .iter()
        .all(|(_, q)| q.bitvector.is_none()));
    assert!(matches!(
        &generated[1].kind,
        CheckKind::BitvectorAssert {
            architecture_specialized: true,
            ..
        }
    ));
}

fn bv_if(cond: Expr, then_block: Vec<Stmt>, else_block: Vec<Stmt>) -> Stmt {
    Stmt::new(
        SpanId(0),
        StmtKind::If {
            cond,
            then_block: Block::new(then_block),
            else_block: Block::new(else_block),
        },
    )
}
fn word_eq(width: i128) -> Expr {
    binary(
        BinOp::Eq,
        Expr::new(
            Ty::Int(IntRange::U(32)),
            SpanId(0),
            ExprKind::IntegerConstant(IntegerConstant::WordBits),
        ),
        Expr::int_lit(width, Ty::Int(IntRange::U(32)), SpanId(0)),
        Ty::Bool,
    )
}
fn assert_real_cases(check: &Check) {
    if let Some(cases) = &check.query.architectures {
        assert_eq!(cases.iter().map(|(w, _)| *w).collect::<Vec<_>>(), [32, 64]);
        for (width, question) in cases {
            let native = question
                .bitvector
                .as_ref()
                .expect("a true placeholder is not an isolated obligation");
            assert_eq!(native.len(), 1);
            assert_eq!(native[0].architecture, *width);
        }
    } else {
        assert_eq!(check.query.bitvector.as_ref().unwrap().len(), 1);
    }
}
#[test]
fn dead_outer_paths_retain_true_and_false_isolated_source_questions() {
    for goal in [false, true] {
        let inner = isolated(
            Expr::bool_lit(goal, SpanId(0)),
            vec![],
            Architecture::Either32Or64,
        );
        let generated = checks(&source(
            Architecture::Either32Or64,
            proof(
                Ty::Bool,
                vec![bv_if(Expr::bool_lit(false, SpanId(0)), vec![inner], vec![])],
            ),
        ));
        assert_eq!(generated.len(), 1);
        assert_real_cases(&generated[0]);
        assert_eq!(generated[0].site, SiteId(0));
    }
}
#[test]
fn both_ordinary_width_branches_keep_every_real_isolated_width_case() {
    for branch in [32, 64] {
        let inner = isolated(word_eq(branch), vec![], Architecture::Either32Or64);
        let generated = checks(&source(
            Architecture::Either32Or64,
            proof(Ty::Bool, vec![bv_if(word_eq(branch), vec![inner], vec![])]),
        ));
        assert_eq!(generated.len(), 1);
        assert_real_cases(&generated[0]);
    }
}
#[test]
fn a_conditional_ordinary_return_cannot_erase_a_later_isolated_query() {
    for architecture in [
        Architecture::Either32Or64,
        Architecture::Exactly(32),
        Architecture::Exactly(64),
    ] {
        let before = bv_if(
            word_eq(32),
            vec![Stmt::new(
                SpanId(0),
                StmtKind::Return {
                    value: None,
                    site: SiteId(1),
                },
            )],
            vec![],
        );
        let after = isolated(word_eq(64), vec![], architecture);
        let generated = checks(&source(architecture, proof(Ty::Bool, vec![before, after])));
        assert_eq!(generated.len(), 1);
        assert_real_cases(&generated[0]);
    }
}
#[test]
fn a_genuine_unconditional_sst_return_still_prunes_the_following_bv() {
    let before = Stmt::new(
        SpanId(0),
        StmtKind::Return {
            value: None,
            site: SiteId(1),
        },
    );
    let after = isolated(
        Expr::bool_lit(false, SpanId(0)),
        vec![],
        Architecture::Either32Or64,
    );
    let generated = checks(&source(
        Architecture::Either32Or64,
        proof(Ty::Bool, vec![before, after]),
    ));
    assert!(generated.is_empty());
}
#[test]
fn ordinary_dead_local_initialization_supplies_availability_but_no_bv_value_fact() {
    let ty = Ty::Int(IntRange::U(8));
    let init = Stmt::new(
        SpanId(0),
        StmtKind::Let {
            local: LocalId(2),
            init: Some(Expr::int_lit(3, ty.clone(), SpanId(0))),
        },
    );
    let goal = binary(
        BinOp::Eq,
        read(2, ty.clone()),
        Expr::int_lit(0, ty.clone(), SpanId(0)),
        Ty::Bool,
    );
    let inner = isolated(goal, vec![], Architecture::Either32Or64);
    let mut function = proof(
        Ty::Bool,
        vec![bv_if(
            Expr::bool_lit(false, SpanId(0)),
            vec![init, inner],
            vec![],
        )],
    );
    function.locals.push(LocalDecl {
        name: "dead_x".into(),
        ty,
        mode: Mode::Spec,
        mutable: false,
        kind: LocalKind::Let,
        span: SpanId(0),
    });
    let generated = checks(&source(Architecture::Either32Or64, function));
    assert_eq!(generated.len(), 1);
    assert_real_cases(&generated[0]);
    for (_, query) in generated[0].query.architectures.as_ref().unwrap() {
        let native = &query.bitvector.as_ref().unwrap()[0];
        assert_eq!(native.variables.len(), 1);
        assert!(native.requires.is_empty());
        assert_ne!(native.goal, trust_vc_vcir::bitvector::Term::Bool(true));
    }
}
#[test]
fn nested_blocks_retain_independent_queries_without_reviving_return_suffixes() {
    let skipped = isolated(
        Expr::bool_lit(false, SpanId(0)),
        vec![],
        Architecture::Either32Or64,
    );
    let mut kept = isolated(
        Expr::bool_lit(true, SpanId(0)),
        vec![],
        Architecture::Either32Or64,
    );
    if let StmtKind::AssertBitVector { site, .. } = &mut kept.kind {
        *site = SiteId(4);
    }
    let statement = bv_if(
        word_eq(32),
        vec![
            Stmt::new(
                SpanId(0),
                StmtKind::Return {
                    value: None,
                    site: SiteId(1),
                },
            ),
            skipped,
        ],
        vec![kept],
    );
    let generated = checks(&source(
        Architecture::Either32Or64,
        proof(Ty::Bool, vec![statement]),
    ));
    assert_eq!(generated.len(), 1);
    assert_eq!(generated[0].site, SiteId(4));
    assert_real_cases(&generated[0]);
}
