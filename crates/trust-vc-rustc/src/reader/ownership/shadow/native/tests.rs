//! Actual two-live-context controls for the compiler transaction component.
//!
//! These construct private synthetic program data, not an original-source
//! permission. Passing them must never enable the seven Proof controls.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::super::program::*;
use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
mod body_correspondence;
mod compiler_auxiliaries;
mod struct_layouts;
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-vc-native-shadow-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

struct Original {
    program: Option<Program>,
    argv: Vec<String>,
    child_directory: PathBuf,
    observation: Option<Observation>,
    source_continued: bool,
    source_analysis: bool,
    tamper: Option<fn(&mut EmittedProgram)>,
    correspondence: Correspondence,
}
impl Callbacks for Original {
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let roots = tcx.hir_body_owners().collect::<Vec<_>>();
        assert_eq!(roots.len(), 1);
        let original = roots[0];
        let body = tcx.hir_body_owned_by(original);
        let typeck = tcx.typeck(original);
        // The original context has already consumed canonical THIR for its
        // genuine exhaustiveness check. The worker cannot replace this cache.
        tcx.ensure_result().check_match(original).unwrap();
        let (thir, _) = tcx.thir_body(original).unwrap();
        assert!(!thir.is_stolen() && tcx.dcx().has_errors().is_none());
        let program = self.program.take().unwrap();
        let recipe = Recipe {
            argv: self.argv.clone(),
            source: self.child_directory.join("shadow.rs"),
            output: self.child_directory.clone(),
            effective_frontend: tcx.sess.opts.jobs.frontend.map(|jobs| jobs.get()),
        };
        let observation = match (self.correspondence, self.tamper) {
            (Correspondence::Declarations, Some(tamper)) => {
                observe_with_transform(program, recipe, tamper)
            }
            (Correspondence::Declarations, None) => observe(program, recipe),
            (Correspondence::OrdinaryBodies, Some(tamper)) => {
                observe_body_roles_with_transform(program, recipe, tamper)
            }
            (Correspondence::OrdinaryBodies, None) => observe_body_roles(program, recipe),
        }
        .unwrap();
        assert!(std::ptr::eq(tcx.hir_body_owned_by(original), body));
        assert!(std::ptr::eq(tcx.typeck(original), typeck));
        assert!(std::ptr::eq(tcx.thir_body(original).unwrap().0, thir));
        assert!(!thir.is_stolen() && tcx.dcx().has_errors().is_none());
        assert!(tcx.mir_borrowck(original).is_ok());
        assert!(tcx.dcx().has_errors().is_none());
        self.source_continued = true;
        self.observation = Some(observation);
        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        self.source_analysis = true;
        Compilation::Stop
    }
}

fn run(program: Program) -> Observation {
    run_with_tamper(program, None)
}

fn run_with_tamper(program: Program, tamper: Option<fn(&mut EmittedProgram)>) -> Observation {
    run_policy(program, tamper, Correspondence::Declarations)
}

fn run_policy(
    program: Program,
    tamper: Option<fn(&mut EmittedProgram)>,
    correspondence: Correspondence,
) -> Observation {
    let directory = Directory::new();
    let source = directory.0.join("original.rs");
    std::fs::write(&source, "pub fn original(value: u8) -> u8 { value }\n").unwrap();
    let child_directory = directory.0.join("fresh");
    std::fs::create_dir(&child_directory).unwrap();
    let argv = vec![
        "native-shadow-live-context-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_shadow_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        source.to_str().unwrap().into(),
    ];
    let mut original = Original {
        program: Some(program),
        argv: argv.clone(),
        child_directory,
        observation: None,
        source_continued: false,
        source_analysis: false,
        tamper,
        correspondence,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut original)).unwrap();
    assert!(original.source_continued && original.source_analysis);
    original.observation.unwrap()
}

fn identity() -> Program {
    Program {
        adts: vec![],
        builtin: None,
        auxiliaries: vec![],
        functions: vec![Function {
            site: Site(0),
            id: FunctionId(0),
            generics: vec![GenericId(0)],
            regions: vec![],
            parameters: vec![Binding {
                site: Site(1),
                id: LocalId(0),
                ty: Type::Parameter(GenericId(0)),
                mutable: false,
            }],
            result: Type::Parameter(GenericId(0)),
            body: Expr {
                site: Site(2),
                kind: ExprKind::Local(LocalId(0)),
            },
        }],
    }
}

#[test]
fn fresh_native_context_returns_and_original_cached_context_continues() {
    let observed = run(identity());
    assert!(
        observed.compiler_returned_ok && observed.expanded && observed.analysis,
        "{observed:?}"
    );
    assert_eq!(observed.typed_roots, BTreeSet::from([FunctionId(0)]));
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
    assert!(
        observed.errors.is_empty() && observed.refusal.is_none(),
        "{observed:?}"
    );
}

#[test]
fn fresh_native_borrow_failure_does_not_taint_the_live_original_context() {
    let consume = Function {
        site: Site(0),
        id: FunctionId(0),
        generics: vec![GenericId(0)],
        regions: vec![],
        parameters: vec![Binding {
            site: Site(1),
            id: LocalId(0),
            ty: Type::Parameter(GenericId(0)),
            mutable: false,
        }],
        result: Type::Unit,
        body: Expr {
            site: Site(2),
            kind: ExprKind::Unit,
        },
    };
    let caller = Function {
        site: Site(3),
        id: FunctionId(1),
        generics: vec![GenericId(1)],
        regions: vec![],
        parameters: vec![Binding {
            site: Site(4),
            id: LocalId(0),
            ty: Type::Parameter(GenericId(1)),
            mutable: false,
        }],
        result: Type::Unit,
        body: Expr {
            site: Site(5),
            kind: ExprKind::Block {
                statements: vec![
                    Statement::Expression(Expr {
                        site: Site(6),
                        kind: ExprKind::Call {
                            function: FunctionId(0),
                            types: vec![Type::Parameter(GenericId(1))],
                            arguments: vec![Expr {
                                site: Site(7),
                                kind: ExprKind::Local(LocalId(0)),
                            }],
                        },
                    }),
                    Statement::Expression(Expr {
                        site: Site(8),
                        kind: ExprKind::Call {
                            function: FunctionId(0),
                            types: vec![Type::Parameter(GenericId(1))],
                            arguments: vec![Expr {
                                site: Site(9),
                                kind: ExprKind::Local(LocalId(0)),
                            }],
                        },
                    }),
                ],
                tail: None,
            },
        },
    };
    let observed = run(Program {
        adts: vec![],
        builtin: None,
        auxiliaries: vec![],
        functions: vec![consume, caller],
    });
    assert!(
        !observed.compiler_returned_ok && observed.expanded && !observed.analysis,
        "{observed:?}"
    );
    assert!(
        observed.errors.iter().any(|error| error == "E0382"),
        "{observed:?}"
    );
    assert_eq!(observed.typed_roots.len(), 2);
    assert_eq!(
        observed.borrow_queries.get(&FunctionId(1)),
        Some(&false),
        "{observed:?}"
    );
    assert!(observed.refusal.is_none(), "{observed:?}");
}

#[test]
fn fresh_native_type_error_cannot_be_reported_as_a_borrow_checked_root() {
    let mut program = identity();
    program.functions[0].generics.clear();
    program.functions[0].parameters[0].ty = Type::Unsigned(Unsigned::U8);
    program.functions[0].result = Type::Bool;
    let observed = run(program);
    assert!(
        !observed.compiler_returned_ok && !observed.analysis,
        "{observed:?}"
    );
    assert!(
        observed.errors.iter().any(|error| error == "E0308"),
        "{observed:?}"
    );
    assert!(
        observed.typed_roots.is_empty()
            && observed.borrow_queries.is_empty()
            && observed.refusal.is_some(),
        "{observed:?}"
    );
}

#[test]
fn real_native_generic_enum_match_has_its_own_published_root_and_borrow_query() {
    let adt = Adt {
        site: Site(0),
        id: AdtId(0),
        kind: AdtKind::Enum,
        generics: vec![GenericId(0), GenericId(1)],
        variants: vec![
            Variant {
                site: Site(1),
                fields: vec![
                    Field {
                        site: Site(2),
                        ty: Type::Parameter(GenericId(0)),
                    },
                    Field {
                        site: Site(3),
                        ty: Type::Parameter(GenericId(1)),
                    },
                ],
            },
            Variant {
                site: Site(4),
                fields: vec![
                    Field {
                        site: Site(5),
                        ty: Type::Parameter(GenericId(0)),
                    },
                    Field {
                        site: Site(6),
                        ty: Type::Parameter(GenericId(1)),
                    },
                ],
            },
        ],
    };
    let binding = |site, id, generic| Binding {
        site: Site(site),
        id: LocalId(id),
        ty: Type::Parameter(GenericId(generic)),
        mutable: false,
    };
    let function = Function {
        site: Site(7),
        id: FunctionId(0),
        generics: vec![GenericId(2), GenericId(3)],
        regions: vec![],
        parameters: vec![Binding {
            site: Site(8),
            id: LocalId(0),
            ty: Type::Adt(
                AdtId(0),
                vec![Type::Parameter(GenericId(2)), Type::Parameter(GenericId(3))],
            ),
            mutable: false,
        }],
        result: Type::Parameter(GenericId(2)),
        body: Expr {
            site: Site(9),
            kind: ExprKind::Match {
                scrutinee: Box::new(Expr {
                    site: Site(10),
                    kind: ExprKind::Local(LocalId(0)),
                }),
                arms: vec![
                    Arm {
                        site: Site(11),
                        pattern: Pattern {
                            site: Site(12),
                            kind: PatternKind::Variant {
                                adt: AdtId(0),
                                variant: 0,
                                fields: vec![
                                    Pattern {
                                        site: Site(13),
                                        kind: PatternKind::Binding(binding(14, 1, 2)),
                                    },
                                    Pattern {
                                        site: Site(15),
                                        kind: PatternKind::Binding(binding(16, 2, 3)),
                                    },
                                ],
                            },
                        },
                        body: Expr {
                            site: Site(17),
                            kind: ExprKind::Local(LocalId(1)),
                        },
                    },
                    Arm {
                        site: Site(18),
                        pattern: Pattern {
                            site: Site(19),
                            kind: PatternKind::Variant {
                                adt: AdtId(0),
                                variant: 1,
                                fields: vec![
                                    Pattern {
                                        site: Site(20),
                                        kind: PatternKind::Binding(binding(21, 3, 2)),
                                    },
                                    Pattern {
                                        site: Site(22),
                                        kind: PatternKind::Binding(binding(23, 4, 3)),
                                    },
                                ],
                            },
                        },
                        body: Expr {
                            site: Site(24),
                            kind: ExprKind::Local(LocalId(3)),
                        },
                    },
                ],
            },
        },
    };
    let observed = run(Program {
        adts: vec![adt],
        functions: vec![function],
        builtin: None,
        auxiliaries: vec![],
    });
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
}

#[test]
fn erased_observation_cannot_materialize_without_planned_native_auxiliaries() {
    let mut program = identity();
    program.functions[0].body = Expr {
        site: Site(2),
        kind: ExprKind::Observe {
            reads: vec![],
            result: Inhabited::Bool,
        },
    };
    let error = program.emit().err().unwrap();
    assert!(
        error.contains("planned compiler-owned auxiliary declarations"),
        "{error}"
    );
}

#[test]
fn native_never_proxy_is_refused_before_any_compiler_or_file_creation() {
    let mut program = identity();
    program.functions[0].body = Expr {
        site: Site(2),
        kind: ExprKind::Block {
            statements: vec![Statement::Shadow {
                binding: Binding {
                    site: Site(3),
                    id: LocalId(1),
                    ty: Type::Never,
                    mutable: false,
                },
            }],
            tail: None,
        },
    };
    let error = program.emit().err().unwrap();
    assert!(error.contains("native never"), "{error}");
}
