//! Real parser/HIR/body controls. These create no original-source permission.
use super::*;

fn pair(generic: bool, construct: bool) -> Program {
    let ty = if generic {
        Type::Parameter(GenericId(0))
    } else {
        Type::Unsigned(Unsigned::U8)
    };
    let function_ty = if generic {
        Type::Parameter(GenericId(1))
    } else {
        ty.clone()
    };
    let parameters = vec![
        Binding {
            site: Site(10),
            id: LocalId(0),
            ty: function_ty.clone(),
            mutable: false,
        },
        Binding {
            site: Site(11),
            id: LocalId(1),
            ty: function_ty.clone(),
            mutable: false,
        },
    ];
    let arguments = if generic {
        vec![function_ty.clone()]
    } else {
        vec![]
    };
    let local = |site, id| Expr {
        site: Site(site),
        kind: ExprKind::Local(LocalId(id)),
    };
    let record = Expr {
        site: Site(20),
        kind: ExprKind::ConstructStruct {
            adt: AdtId(0),
            types: arguments.clone(),
            fields: vec![(1, local(21, 1)), (0, local(22, 0))],
        },
    };
    let (result, body) = if construct {
        (Type::Adt(AdtId(0), arguments), record)
    } else {
        (
            Type::Tuple(vec![function_ty.clone(), function_ty.clone()]),
            Expr {
                site: Site(30),
                kind: ExprKind::Block {
                    statements: vec![Statement::Let {
                        binding: Binding {
                            site: Site(31),
                            id: LocalId(2),
                            ty: Type::Adt(AdtId(0), arguments.clone()),
                            mutable: true,
                        },
                        initializer: Some(record),
                    }],
                    tail: Some(Box::new(Expr {
                        site: Site(32),
                        kind: ExprKind::Tuple(vec![
                            Expr {
                                site: Site(33),
                                kind: ExprKind::StructField {
                                    base: Box::new(local(34, 2)),
                                    adt: AdtId(0),
                                    types: arguments.clone(),
                                    field: 0,
                                },
                            },
                            Expr {
                                site: Site(35),
                                kind: ExprKind::StructField {
                                    base: Box::new(local(36, 2)),
                                    adt: AdtId(0),
                                    types: arguments,
                                    field: 1,
                                },
                            },
                        ]),
                    })),
                },
            },
        )
    };
    Program {
        adts: vec![Adt {
            site: Site(0),
            id: AdtId(0),
            kind: AdtKind::Struct,
            generics: if generic { vec![GenericId(0)] } else { vec![] },
            variants: vec![Variant {
                site: Site(1),
                fields: vec![
                    Field {
                        site: Site(2),
                        ty: ty.clone(),
                    },
                    Field { site: Site(3), ty },
                ],
            }],
        }],
        functions: vec![Function {
            site: Site(4),
            id: FunctionId(0),
            generics: if generic { vec![GenericId(1)] } else { vec![] },
            regions: vec![],
            parameters,
            result,
            body,
        }],
        builtin: None,
        auxiliaries: vec![],
    }
}

fn strict(program: Program, tamper: Option<fn(&mut EmittedProgram)>) -> Observation {
    run_policy(program, tamper, Correspondence::OrdinaryBodies)
}

#[test]
fn actual_ordinary_parser_and_hir_roles_close_before_native_partial_move_checks() {
    let program = pair(true, false);
    let roles = program
        .emit()
        .unwrap()
        .roles
        .into_keys()
        .collect::<BTreeSet<_>>();
    let observed = strict(program, None);
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert_eq!(observed.checked_body_roles, roles);
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
    assert!(observed.errors.is_empty());
}

#[test]
fn actual_struct_constructor_preserves_written_field_edges_in_the_live_native_body() {
    let program = pair(false, true);
    let roles = program
        .emit()
        .unwrap()
        .roles
        .into_keys()
        .collect::<BTreeSet<_>>();
    let observed = strict(program, None);
    assert!(
        observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert_eq!(observed.checked_body_roles, roles);
}

fn duplicate_second_read(emitted: &mut EmittedProgram) {
    let range = emitted.roles[&(Site(35), Role::Expression)];
    let original = &emitted.source[range.start..range.end];
    assert!(original.ends_with("__field_0_1"));
    let replacement = original.replace("__field_0_1", "__field_0_0");
    assert_eq!(replacement.len(), original.len());
    emitted
        .source
        .replace_range(range.start..range.end, &replacement);
}

#[test]
fn equal_typed_field_substitution_is_rejected_by_actual_body_correspondence() {
    let observed = strict(pair(false, false), Some(duplicate_second_read));
    assert!(
        observed.refusal.is_some(),
        "a type-correct wrong field must not become a correspondence result: {observed:?}"
    );
    assert!(observed.checked_body_roles.is_empty() && observed.borrow_queries.is_empty());
}

fn duplicate_constructor_argument(emitted: &mut EmittedProgram) {
    let range = emitted.roles[&(Site(21), Role::Expression)];
    assert_eq!(&emitted.source[range.start..range.end], "__local_1");
    emitted
        .source
        .replace_range(range.start..range.end, "__local_0");
}

#[test]
fn equal_typed_local_substitution_is_rejected_by_actual_native_binding_resolution() {
    let observed = strict(pair(false, true), Some(duplicate_constructor_argument));
    assert!(
        observed.refusal.is_some(),
        "a type-correct wrong local must not become a correspondence result: {observed:?}"
    );
    assert!(observed.checked_body_roles.is_empty() && observed.borrow_queries.is_empty());
}

fn assignment() -> Program {
    let mut program = pair(false, false);
    let ExprKind::Block { statements, .. } = &mut program.functions[0].body.kind else {
        panic!()
    };
    statements.push(Statement::Expression(Expr {
        site: Site(40),
        kind: ExprKind::AssignPlace {
            destination: Box::new(Expr {
                site: Site(41),
                kind: ExprKind::StructField {
                    base: Box::new(Expr {
                        site: Site(42),
                        kind: ExprKind::Local(LocalId(2)),
                    }),
                    adt: AdtId(0),
                    types: vec![],
                    field: 0,
                },
            }),
            value: Box::new(Expr {
                site: Site(43),
                kind: ExprKind::Local(LocalId(0)),
            }),
        },
    }));
    program
}

#[test]
fn actual_field_assignment_joins_its_complete_native_place_and_value_edges() {
    let program = assignment();
    let roles = program
        .emit()
        .unwrap()
        .roles
        .into_keys()
        .collect::<BTreeSet<_>>();
    let observed = strict(program, None);
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert_eq!(observed.checked_body_roles, roles);
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
}

fn wrong_assignment_field(emitted: &mut EmittedProgram) {
    let range = emitted.roles[&(Site(41), Role::Expression)];
    let original = &emitted.source[range.start..range.end];
    assert!(original.contains("__field_0_0"));
    let replacement = original.replace("__field_0_0", "__field_0_1");
    assert_eq!(replacement.len(), original.len());
    emitted
        .source
        .replace_range(range.start..range.end, &replacement);
}

#[test]
fn equal_typed_assignment_to_a_sibling_field_is_not_the_issued_native_place() {
    let observed = strict(assignment(), Some(wrong_assignment_field));
    assert!(
        observed.refusal.is_some(),
        "a type-correct wrong assignment must not join: {observed:?}"
    );
    assert!(observed.checked_body_roles.is_empty() && observed.borrow_queries.is_empty());
}

fn direct_call() -> Program {
    let mut program = identity();
    program.functions.push(Function {
        site: Site(10),
        id: FunctionId(1),
        generics: vec![GenericId(1)],
        regions: vec![],
        parameters: vec![Binding {
            site: Site(11),
            id: LocalId(0),
            ty: Type::Parameter(GenericId(1)),
            mutable: false,
        }],
        result: Type::Parameter(GenericId(1)),
        body: Expr {
            site: Site(12),
            kind: ExprKind::Call {
                function: FunctionId(0),
                types: vec![Type::Parameter(GenericId(1))],
                arguments: vec![Expr {
                    site: Site(13),
                    kind: ExprKind::Local(LocalId(0)),
                }],
            },
        },
    });
    program
}

#[test]
fn actual_direct_call_keeps_its_allocated_native_target_and_full_generic_arguments() {
    let program = direct_call();
    let roles = program
        .emit()
        .unwrap()
        .roles
        .into_keys()
        .collect::<BTreeSet<_>>();
    let observed = strict(program, None);
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.refusal.is_none(),
        "{observed:?}"
    );
    assert_eq!(observed.checked_body_roles, roles);
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true), (FunctionId(1), true)])
    );
}

fn substitute_same_signature_callee(emitted: &mut EmittedProgram) {
    let range = emitted.roles[&(Site(12), Role::Expression)];
    let original = &emitted.source[range.start..range.end];
    assert!(original.contains("__function_0"));
    let replacement = original.replace("__function_0", "__function_1");
    assert_eq!(replacement.len(), original.len());
    emitted
        .source
        .replace_range(range.start..range.end, &replacement);
}

#[test]
fn an_equal_signature_callee_cannot_replace_the_actual_issued_function() {
    let observed = strict(direct_call(), Some(substitute_same_signature_callee));
    assert!(
        observed.refusal.is_some(),
        "a native callee substitution must not join: {observed:?}"
    );
    assert!(observed.checked_body_roles.is_empty() && observed.borrow_queries.is_empty());
}
