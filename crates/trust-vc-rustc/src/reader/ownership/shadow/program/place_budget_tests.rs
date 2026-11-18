//! Assignment-place grammar shares the complete structural work allowance.
use super::*;

fn local() -> Expr {
    Expr {
        site: Site(0),
        kind: ExprKind::Local(LocalId(0)),
    }
}

fn fields(count: usize) -> Expr {
    let mut value = local();
    for index in 0..count {
        value = Expr {
            site: Site(index as u32 + 1),
            kind: if index % 2 == 0 {
                ExprKind::TupleField {
                    base: Box::new(value),
                    field: 0,
                }
            } else {
                ExprKind::StructField {
                    base: Box::new(value),
                    adt: AdtId(0),
                    types: vec![],
                    field: 0,
                }
            },
        };
    }
    value
}

#[test]
fn assignment_place_grammar_debits_the_existing_allowance_before_each_node() {
    let value = fields(2);
    let mut zero = 0;
    assert!(program_place(&value, &mut zero, 0).is_err());
    assert_eq!(zero, 0);
    let mut short = 2;
    assert!(program_place(&value, &mut short, 0).is_err());
    assert_eq!(short, 0);
    let mut exact = 3;
    assert!(program_place(&value, &mut exact, 0).unwrap());
    assert_eq!(exact, 0);
    assert!(program_place(&value, &mut exact, 0).is_err());
}

#[test]
fn assignment_place_grammar_checks_depth_before_walking_a_deeper_field() {
    let deepest = fields(127);
    let mut exact = 128;
    assert!(program_place(&deepest, &mut exact, 0).unwrap());
    assert_eq!(exact, 0);
    let too_deep = fields(128);
    let mut remaining = 129;
    assert!(program_place(&too_deep, &mut remaining, 0).is_err());
    assert_eq!(remaining, 1);
    let mut shifted = 2;
    assert!(program_place(&fields(1), &mut shifted, 127).is_err());
    assert_eq!(shifted, 1);
    let mut invalid_depth = 1;
    assert!(program_place(&local(), &mut invalid_depth, usize::MAX).is_err());
    assert_eq!(invalid_depth, 1);
}

#[test]
fn assignment_place_grammar_retains_local_dereference_and_nonplace_rules() {
    let dereference = Expr {
        site: Site(1),
        kind: ExprKind::Dereference(Box::new(local())),
    };
    for value in [local(), dereference, fields(2)] {
        let mut remaining = 3;
        assert!(program_place(&value, &mut remaining, 0).unwrap());
    }
    for kind in [
        ExprKind::Unit,
        ExprKind::TemporaryScope(Box::new(local())),
        ExprKind::Borrow {
            mutability: Mutability::Mutable,
            value: Box::new(local()),
        },
    ] {
        let value = Expr {
            site: Site(1),
            kind,
        };
        let mut remaining = 1;
        assert!(!program_place(&value, &mut remaining, 0).unwrap());
        assert_eq!(remaining, 0);
    }
}

fn tuple_assignment() -> Program {
    Program {
        adts: vec![],
        functions: vec![Function {
            site: Site(0),
            id: FunctionId(0),
            generics: vec![],
            regions: vec![],
            parameters: vec![Binding {
                site: Site(1),
                id: LocalId(0),
                ty: Type::Tuple(vec![Type::Bool]),
                mutable: true,
            }],
            result: Type::Unit,
            body: Expr {
                site: Site(2),
                kind: ExprKind::AssignPlace {
                    destination: Box::new(Expr {
                        site: Site(3),
                        kind: ExprKind::TupleField {
                            base: Box::new(Expr {
                                site: Site(4),
                                kind: ExprKind::Local(LocalId(0)),
                            }),
                            field: 0,
                        },
                    }),
                    value: Box::new(Expr {
                        site: Site(5),
                        kind: ExprKind::Bool(true),
                    }),
                },
            },
        }],
        builtin: None,
        auxiliaries: vec![],
    }
}

#[test]
fn assignment_validation_includes_grammar_and_expression_work_in_one_budget() {
    let program = tuple_assignment();
    let mut exact = 9;
    assert_eq!(program.validate_with_work(&mut exact).unwrap().len(), 6);
    assert_eq!(exact, 0);
    let mut short = 8;
    assert!(program.validate_with_work(&mut short).is_err());
    assert_eq!(short, 0);
    let mut before_place = 4;
    let error = program.validate_with_work(&mut before_place).unwrap_err();
    assert!(error.contains("shared structural bound"), "{error}");
    assert_eq!(before_place, 0);
    let mut invalid = tuple_assignment();
    let ExprKind::AssignPlace { destination, .. } = &mut invalid.functions[0].body.kind else {
        panic!()
    };
    destination.kind = ExprKind::TemporaryScope(Box::new(Expr {
        site: Site(6),
        kind: ExprKind::Local(LocalId(0)),
    }));
    let error = invalid.validate().unwrap_err();
    assert!(error.contains("not a represented place"), "{error}");
}
