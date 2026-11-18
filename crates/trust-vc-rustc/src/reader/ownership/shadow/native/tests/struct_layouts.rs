//! Private generated-program controls. These never admit original Source.
use super::*;

fn local(site: u32) -> Expr {
    Expr {
        site: Site(site),
        kind: ExprKind::Local(LocalId(0)),
    }
}
fn field(site: u32, base_site: u32, slot: usize, types: Vec<Type>) -> Expr {
    Expr {
        site: Site(site),
        kind: ExprKind::StructField {
            base: Box::new(local(base_site)),
            adt: AdtId(0),
            types,
            field: slot,
        },
    }
}
fn generic_fields(repeat: bool) -> Program {
    let arguments = vec![Type::Parameter(GenericId(2)), Type::Parameter(GenericId(3))];
    Program {
        adts: vec![Adt {
            site: Site(0),
            id: AdtId(0),
            kind: AdtKind::Struct,
            generics: vec![GenericId(0), GenericId(1)],
            variants: vec![Variant {
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
            }],
        }],
        functions: vec![Function {
            site: Site(10),
            id: FunctionId(0),
            generics: vec![GenericId(2), GenericId(3)],
            regions: vec![],
            parameters: vec![Binding {
                site: Site(11),
                id: LocalId(0),
                ty: Type::Adt(AdtId(0), arguments.clone()),
                mutable: false,
            }],
            result: Type::Tuple(vec![
                arguments[0].clone(),
                arguments[if repeat { 0 } else { 1 }].clone(),
            ]),
            body: Expr {
                site: Site(20),
                kind: ExprKind::Tuple(vec![
                    field(21, 22, 0, arguments.clone()),
                    field(23, 24, if repeat { 0 } else { 1 }, arguments),
                ]),
            },
        }],
        builtin: None,
        auxiliaries: vec![],
    }
}

#[test]
fn real_native_struct_fields_preserve_kind_and_partial_generic_moves() {
    let program = generic_fields(false);
    let emitted = program.emit().unwrap();
    assert!(emitted.source.contains("struct __Adt_0"));
    assert!(!emitted.source.contains("enum __Adt_0"));
    let observed = run(program);
    assert!(
        observed.compiler_returned_ok && observed.analysis,
        "{observed:?}"
    );
    assert_eq!(observed.typed_roots, BTreeSet::from([FunctionId(0)]));
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
    assert!(
        observed.refusal.is_none() && observed.errors.is_empty(),
        "{observed:?}"
    );
}

#[test]
fn a_second_consumption_of_the_same_struct_field_is_a_native_move_error() {
    let observed = run(generic_fields(true));
    assert!(!observed.compiler_returned_ok, "{observed:?}");
    assert!(
        observed.errors.iter().any(|error| error == "E0382"),
        "{observed:?}"
    );
}

fn written_fields() -> Program {
    let u8 = Type::Unsigned(Unsigned::U8);
    let u16 = Type::Unsigned(Unsigned::U16);
    let integer = |site, magnitude, ty| Expr {
        site: Site(site),
        kind: ExprKind::Integer { magnitude, ty },
    };
    Program {
        adts: vec![Adt {
            site: Site(0),
            id: AdtId(0),
            kind: AdtKind::Struct,
            generics: vec![],
            variants: vec![Variant {
                site: Site(1),
                fields: vec![
                    Field {
                        site: Site(2),
                        ty: u8.clone(),
                    },
                    Field {
                        site: Site(3),
                        ty: u16.clone(),
                    },
                ],
            }],
        }],
        functions: vec![Function {
            site: Site(10),
            id: FunctionId(0),
            generics: vec![],
            regions: vec![],
            parameters: vec![],
            result: Type::Tuple(vec![u8.clone(), u16.clone()]),
            body: Expr {
                site: Site(11),
                kind: ExprKind::Block {
                    statements: vec![
                        Statement::Let {
                            binding: Binding {
                                site: Site(12),
                                id: LocalId(0),
                                ty: Type::Adt(AdtId(0), vec![]),
                                mutable: true,
                            },
                            initializer: Some(Expr {
                                site: Site(13),
                                kind: ExprKind::ConstructStruct {
                                    adt: AdtId(0),
                                    types: vec![],
                                    fields: vec![
                                        (1, integer(14, 7, u16.clone())),
                                        (0, integer(15, 2, u8.clone())),
                                    ],
                                },
                            }),
                        },
                        Statement::Expression(Expr {
                            site: Site(16),
                            kind: ExprKind::AssignPlace {
                                destination: Box::new(field(17, 18, 0, vec![])),
                                value: Box::new(integer(19, 9, u8)),
                            },
                        }),
                    ],
                    tail: Some(Box::new(Expr {
                        site: Site(20),
                        kind: ExprKind::Tuple(vec![
                            field(21, 22, 0, vec![]),
                            field(23, 24, 1, vec![]),
                        ]),
                    })),
                },
            },
        }],
        builtin: None,
        auxiliaries: vec![],
    }
}

#[test]
fn native_struct_construction_keeps_written_field_order_and_field_writes() {
    let program = written_fields();
    let emitted = program.emit().unwrap();
    let range = emitted.roles[&(Site(13), Role::Expression)];
    let constructor = &emitted.source[range.start..range.end];
    assert!(constructor.find("__field_0_1:").unwrap() < constructor.find("__field_0_0:").unwrap());
    let observed = run(program);
    assert!(
        observed.compiler_returned_ok && observed.analysis && observed.errors.is_empty(),
        "{observed:?}"
    );
    assert_eq!(
        observed.borrow_queries,
        BTreeMap::from([(FunctionId(0), true)])
    );
}

#[test]
fn struct_kind_slots_binders_and_original_work_are_checked_before_emission() {
    let mut wrong_kind = generic_fields(false);
    wrong_kind.adts[0].kind = AdtKind::Enum;
    assert!(wrong_kind.emit().is_err());
    let mut wrong_slot = generic_fields(false);
    wrong_slot.adts[0].variants[0].fields.pop();
    assert!(wrong_slot.emit().is_err());
    let mut wrong_binder = generic_fields(false);
    wrong_binder.functions[0].parameters[0].ty = Type::Adt(AdtId(0), vec![Type::Bool]);
    assert!(wrong_binder.emit().is_err());
    let mut duplicate = written_fields();
    let ExprKind::Block { statements, .. } = &mut duplicate.functions[0].body.kind else {
        panic!()
    };
    let Statement::Let {
        initializer:
            Some(Expr {
                kind: ExprKind::ConstructStruct { fields, .. },
                ..
            }),
        ..
    } = &mut statements[0]
    else {
        panic!()
    };
    fields[1].0 = fields[0].0;
    assert!(duplicate.emit().is_err());
    let program = generic_fields(false);
    let mut remaining = 10_000;
    program.validate_with_work(&mut remaining).unwrap();
    let cost = 10_000 - remaining;
    let mut exact = cost;
    program.validate_with_work(&mut exact).unwrap();
    assert_eq!(exact, 0);
    assert!(program.validate_with_work(&mut exact).is_err());
    let mut short = cost - 1;
    assert!(program.validate_with_work(&mut short).is_err());
    assert_eq!(short, 0);
}
