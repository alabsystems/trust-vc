//! Actual native controls for non-admitting compiler-owned auxiliaries.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

fn declaration(kind: AuxiliaryKind) -> Auxiliary {
    Auxiliary {
        site: Site(100 + kind as u32),
        kind,
    }
}

fn observing() -> Program {
    let mut program = identity();
    program.auxiliaries = vec![
        declaration(AuxiliaryKind::ErasedValue),
        declaration(AuxiliaryKind::ShadowValue),
    ];
    program.functions[0].body = Expr {
        site: Site(2),
        kind: ExprKind::Block {
            statements: vec![
                Statement::Shadow {
                    binding: Binding {
                        site: Site(6),
                        id: LocalId(1),
                        ty: Type::Bool,
                        mutable: false,
                    },
                },
                Statement::Expression(Expr {
                    site: Site(4),
                    kind: ExprKind::Observe {
                        reads: vec![],
                        result: Inhabited::Bool,
                    },
                }),
            ],
            tail: Some(Box::new(Expr {
                site: Site(5),
                kind: ExprKind::Local(LocalId(0)),
            })),
        },
    };
    program
}

fn move_after_auxiliary(tie: bool) -> Program {
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
    let initial = if tie {
        Expr {
            site: Site(30),
            kind: ExprKind::MutableTie {
                first: Box::new(Expr {
                    site: Site(31),
                    kind: ExprKind::Borrow {
                        mutability: Mutability::Mutable,
                        value: Box::new(Expr {
                            site: Site(32),
                            kind: ExprKind::Local(LocalId(1)),
                        }),
                    },
                }),
                second: Box::new(Expr {
                    site: Site(33),
                    kind: ExprKind::Borrow {
                        mutability: Mutability::Mutable,
                        value: Box::new(Expr {
                            site: Site(34),
                            kind: ExprKind::Local(LocalId(2)),
                        }),
                    },
                }),
            },
        }
    } else {
        Expr {
            site: Site(30),
            kind: ExprKind::Observe {
                reads: vec![],
                result: Inhabited::Bool,
            },
        }
    };
    let consume_call = |call, argument| Expr {
        site: Site(call),
        kind: ExprKind::Call {
            function: FunctionId(0),
            types: vec![Type::Parameter(GenericId(1))],
            arguments: vec![Expr {
                site: Site(argument),
                kind: ExprKind::Local(LocalId(0)),
            }],
        },
    };
    let caller = Function {
        site: Site(3),
        id: FunctionId(1),
        generics: vec![GenericId(1)],
        regions: vec![],
        parameters: vec![
            Binding {
                site: Site(4),
                id: LocalId(0),
                ty: Type::Parameter(GenericId(1)),
                mutable: false,
            },
            Binding {
                site: Site(5),
                id: LocalId(1),
                ty: Type::Bool,
                mutable: true,
            },
            Binding {
                site: Site(6),
                id: LocalId(2),
                ty: Type::Bool,
                mutable: true,
            },
        ],
        result: Type::Unit,
        body: Expr {
            site: Site(20),
            kind: ExprKind::Block {
                statements: vec![
                    Statement::Expression(initial),
                    Statement::Expression(consume_call(21, 22)),
                    Statement::Expression(consume_call(23, 24)),
                ],
                tail: None,
            },
        },
    };
    Program {
        adts: vec![],
        functions: vec![consume, caller],
        builtin: None,
        auxiliaries: vec![declaration(if tie {
            AuxiliaryKind::MutableTie
        } else {
            AuxiliaryKind::ErasedValue
        })],
    }
}

#[test]
fn compiler_owned_value_roots_have_real_types_calls_and_native_borrow_queries() {
    let observed = run(observing());
    assert!(
        observed.compiler_returned_ok && observed.expanded && observed.analysis,
        "{observed:?}"
    );
    assert!(
        observed.refusal.is_none() && observed.errors.is_empty(),
        "{observed:?}"
    );
    assert_eq!(
        observed.typed_auxiliaries,
        BTreeSet::from([AuxiliaryKind::ErasedValue, AuxiliaryKind::ShadowValue])
    );
    assert_eq!(
        observed.auxiliary_borrow_queries,
        BTreeMap::from([
            (AuxiliaryKind::ErasedValue, true),
            (AuxiliaryKind::ShadowValue, true)
        ])
    );
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
}

#[test]
fn many_real_auxiliary_calls_compare_the_actual_source_bytes_once() {
    let mut program = observing();
    let ExprKind::Block { statements, .. } = &mut program.functions[0].body.kind else {
        unreachable!();
    };
    for index in 0..64 {
        statements.push(Statement::Expression(Expr {
            site: Site(1_000 + index),
            kind: ExprKind::Observe {
                reads: vec![],
                result: Inhabited::Unit,
            },
        }));
    }
    let observed = run(program);
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert!(
        observed.errors.is_empty() && observed.borrow_queries.values().all(|checked| *checked),
        "{observed:?}"
    );
    assert_eq!(observed.auxiliary_borrow_queries.len(), 2);
    assert!(observed
        .auxiliary_borrow_queries
        .values()
        .all(|checked| *checked));
    assert_eq!(observed.full_source_byte_comparisons, 1);
}

#[test]
fn generic_caller_parameters_and_free_borrow_regions_are_preserved_in_auxiliary_arguments() {
    let mut program = identity();
    program.auxiliaries = vec![
        declaration(AuxiliaryKind::ErasedValue),
        declaration(AuxiliaryKind::ShadowValue),
    ];
    program.functions[0].body = Expr {
        site: Site(2),
        kind: ExprKind::Block {
            statements: vec![
                Statement::Shadow {
                    binding: Binding {
                        site: Site(3),
                        id: LocalId(1),
                        ty: Type::Parameter(GenericId(0)),
                        mutable: false,
                    },
                },
                Statement::Expression(Expr {
                    site: Site(4),
                    kind: ExprKind::Observe {
                        reads: vec![Expr {
                            site: Site(5),
                            kind: ExprKind::Borrow {
                                mutability: Mutability::Shared,
                                value: Box::new(Expr {
                                    site: Site(6),
                                    kind: ExprKind::Local(LocalId(1)),
                                }),
                            },
                        }],
                        result: Inhabited::Unit,
                    },
                }),
            ],
            tail: Some(Box::new(Expr {
                site: Site(7),
                kind: ExprKind::Local(LocalId(0)),
            })),
        },
    };
    let observed = run(program);
    assert!(
        observed.compiler_returned_ok
            && observed.analysis
            && observed.refusal.is_none()
            && observed.errors.is_empty(),
        "{observed:?}"
    );
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
    assert_eq!(
        observed.auxiliary_borrow_queries,
        BTreeMap::from([
            (AuxiliaryKind::ErasedValue, true),
            (AuxiliaryKind::ShadowValue, true)
        ])
    );
}

fn assert_post_call_move_failure(tie: bool) {
    let observed = run(move_after_auxiliary(tie));
    assert!(
        !observed.compiler_returned_ok && observed.expanded && !observed.analysis,
        "{observed:?}"
    );
    assert!(observed.refusal.is_none(), "{observed:?}");
    assert!(
        observed.errors.iter().any(|code| code == "E0382"),
        "{observed:?}"
    );
    assert_eq!(
        observed.borrow_queries.get(&FunctionId(1)),
        Some(&false),
        "{observed:?}"
    );
    assert_eq!(
        observed.typed_auxiliaries,
        BTreeSet::from([if tie {
            AuxiliaryKind::MutableTie
        } else {
            AuxiliaryKind::ErasedValue
        }])
    );
}

#[test]
fn diverging_value_producer_does_not_hide_a_later_native_double_move() {
    assert_post_call_move_failure(false);
}

#[test]
fn mutable_tie_call_does_not_hide_a_later_native_double_move() {
    assert_post_call_move_failure(true);
}

#[test]
fn conservative_same_region_tie_retains_the_second_loan_effect() {
    let borrow = |site, local| Expr {
        site: Site(site),
        kind: ExprKind::Borrow {
            mutability: Mutability::Mutable,
            value: Box::new(Expr {
                site: Site(site + 1),
                kind: ExprKind::Local(LocalId(local)),
            }),
        },
    };
    let program = Program {
        adts: vec![],
        builtin: None,
        auxiliaries: vec![declaration(AuxiliaryKind::MutableTie)],
        functions: vec![Function {
            site: Site(0),
            id: FunctionId(0),
            generics: vec![],
            regions: vec![],
            parameters: vec![
                Binding {
                    site: Site(1),
                    id: LocalId(0),
                    ty: Type::Bool,
                    mutable: true,
                },
                Binding {
                    site: Site(2),
                    id: LocalId(1),
                    ty: Type::Bool,
                    mutable: true,
                },
            ],
            result: Type::Unit,
            body: Expr {
                site: Site(3),
                kind: ExprKind::Block {
                    statements: vec![Statement::Expression(Expr {
                        site: Site(4),
                        kind: ExprKind::Tuple(vec![
                            Expr {
                                site: Site(5),
                                kind: ExprKind::MutableTie {
                                    first: Box::new(borrow(6, 0)),
                                    second: Box::new(borrow(8, 1)),
                                },
                            },
                            borrow(10, 1),
                        ]),
                    })],
                    tail: None,
                },
            },
        }],
    };
    let observed = run(program);
    assert!(
        !observed.compiler_returned_ok && !observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert!(
        observed.errors.iter().any(|code| code == "E0499"),
        "{observed:?}"
    );
    // This is the deliberately stricter same-region mechanics contract. It
    // cannot invent that equality in a later source/generic region mapping.
}

/// Test-only edits preserve the exact updated input-role ranges, so rejection
/// must come from the real native allocation/signature/body/call relationship,
/// not merely stale source lengths or bytes.
fn replace(emitted: &mut EmittedProgram, start: usize, end: usize, value: &str) {
    emitted.source.replace_range(start..end, value);
    let delta = value.len() as isize - (end - start) as isize;
    for range in emitted.roles.values_mut() {
        if range.start >= end {
            range.start = range.start.checked_add_signed(delta).unwrap();
            range.end = range.end.checked_add_signed(delta).unwrap();
        } else if range.end > start {
            assert!(range.start <= start && range.end >= end);
            range.end = range.end.checked_add_signed(delta).unwrap();
        }
    }
}
fn auxiliary_edit(emitted: &mut EmittedProgram, kind: AuxiliaryKind, before: &str, after: &str) {
    let role = emitted.roles[&(declaration(kind).site, Role::Auxiliary)];
    let relative = emitted.source[role.start..role.end].find(before).unwrap();
    replace(
        emitted,
        role.start + relative,
        role.start + relative + before.len(),
        after,
    );
}
fn assert_refused(program: Program, expected_reason: &str, tamper: fn(&mut EmittedProgram)) {
    let observed = run_with_tamper(program, Some(tamper));
    assert!(
        !observed.analysis && observed.refusal.is_some(),
        "{observed:?}"
    );
    assert!(
        observed.borrow_queries.is_empty() && observed.auxiliary_borrow_queries.is_empty(),
        "{observed:?}"
    );
    assert!(
        observed
            .refusal
            .as_ref()
            .is_some_and(|reason| reason.starts_with(expected_reason)),
        "expected {expected_reason:?}, actual {observed:?}"
    );
}

#[test]
fn same_name_signature_and_body_in_another_allocation_cannot_replace_the_auxiliary() {
    assert_refused(
        observing(),
        "a planned auxiliary call changed its actual native allocation/relationship",
        |emitted| {
            let root = emitted.roles[&(Site(0), Role::Function)];
            let start = root.start + emitted.source[root.start..root.end].find('{').unwrap() + 1;
            replace(
            emitted,
            start,
            start,
            "fn __compiler_erased_value<__Source,__Target>(__source:__Source)->__Target{loop{}}\n",
        );
        },
    );
}

#[test]
fn same_signature_value_producer_with_another_native_body_is_refused() {
    assert_refused(
        observing(),
        "a compiler value producer has an unplanned native body",
        |emitted| {
            auxiliary_edit(
                emitted,
                AuxiliaryKind::ErasedValue,
                "loop{}",
                "loop{continue;}",
            )
        },
    );
}

#[test]
fn same_signature_tie_with_extra_body_statements_is_refused() {
    assert_refused(
        move_after_auxiliary(true),
        "the compiler auxiliary has unplanned body statements or no tail",
        |emitted| {
            auxiliary_edit(
                emitted,
                AuxiliaryKind::MutableTie,
                "{__first}",
                "{let __extra=();__first}",
            )
        },
    );
}

#[test]
fn mutable_tie_cannot_return_the_second_native_input() {
    assert_refused(
        move_after_auxiliary(true),
        "a compiler tie laundered its input/result region or referent relationship",
        |emitted| {
            auxiliary_edit(
                emitted,
                AuxiliaryKind::MutableTie,
                ")->&'__tie mut __First{__first}",
                ")->&'__tie mut __Second{__second}",
            )
        },
    );
}

#[test]
fn mutable_tie_cannot_launder_the_second_native_loan_into_another_region() {
    assert_refused(
        move_after_auxiliary(true),
        "a compiler auxiliary changed its bound native regions",
        |emitted| {
            auxiliary_edit(
                emitted,
                AuxiliaryKind::MutableTie,
                "<'__tie,",
                "<'__tie,'__other,",
            );
            auxiliary_edit(
                emitted,
                AuxiliaryKind::MutableTie,
                "__second:&'__tie",
                "__second:&'__other",
            );
        },
    );
}

#[test]
fn nested_direct_parser_parentheses_preserve_the_unique_native_call() {
    let observed = run_with_tamper(
        observing(),
        Some(|emitted| {
            let role = emitted.roles[&(Site(4), Role::Expression)];
            // Keep the issued role on the actual inner call, while the parser
            // allocates another direct parent with its own NodeId and span.
            replace(emitted, role.end, role.end, ")");
            replace(emitted, role.start, role.start, "(");
        }),
    );
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert!(
        observed.borrow_queries.values().all(|checked| *checked)
            && observed.auxiliary_borrow_queries.len() == 2
            && observed
                .auxiliary_borrow_queries
                .values()
                .all(|checked| *checked),
        "{observed:?}"
    );
}

#[test]
fn a_containing_nonparen_block_cannot_substitute_for_the_issued_call() {
    assert_refused(
        observing(),
        "an actual auxiliary AST call has no issued inner range",
        |emitted| {
            let role = emitted.roles[&(Site(4), Role::Expression)];
            let original = emitted.source[role.start..role.end].to_owned();
            // This role now covers a containing block rather than the Call.
            // A generic containment matcher would accidentally accept it.
            replace(emitted, role.start, role.end, &format!("{{{original}}}"));
        },
    );
}

#[test]
fn an_unused_value_call_cannot_change_its_planned_native_type_argument() {
    assert_refused(
        observing(),
        "a compiler value call changed its planned target type",
        |emitted| {
            let role = emitted.roles[&(Site(4), Role::Expression)];
            let relative = emitted.source[role.start..role.end]
                .find("::<_,bool>")
                .unwrap();
            let start = role.start + relative;
            replace(emitted, start, start + "::<_,bool>".len(), "::<_,u8>");
        },
    );
}

#[test]
fn uninhabited_shadow_field_is_refused_before_native_materialization() {
    let mut program = observing();
    program.adts.push(Adt {
        site: Site(200),
        id: AdtId(0),
        kind: AdtKind::Enum,
        generics: vec![],
        variants: vec![Variant {
            site: Site(201),
            fields: vec![Field {
                site: Site(202),
                ty: Type::Never,
            }],
        }],
    });
    let ExprKind::Block { statements, .. } = &mut program.functions[0].body.kind else {
        panic!()
    };
    let Statement::Shadow { binding } = &mut statements[0] else {
        panic!()
    };
    binding.ty = Type::Adt(AdtId(0), vec![]);
    assert!(program.emit().err().unwrap().contains("native never"));
}
