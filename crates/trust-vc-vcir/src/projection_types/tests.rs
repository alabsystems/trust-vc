use super::*;
use crate::{DefHash, SpanId};

fn member(n: u64) -> ProjectionId { ProjectionId(DefHash::new(10, n)) }
fn projection(n: u64, args: Vec<Ty>) -> Ty { Ty::Projection(member(n), args) }
fn source() -> VcCrate {
    let mut source = VcCrate::new("closed implementation semantics");
    source.projections = [1, 2].map(|n| ProjectionDecl {
        id: member(n), trait_id: DefHash::new(11, 0), arity: 2,
        name: "same diagnostic name".into(), span: SpanId(0),
    }).to_vec();
    source.projection_impls.push(ProjectionImpl {
        id: DefHash::new(12, 1), trait_id: DefHash::new(11, 0),
        arguments: vec![Ty::uint(8), Ty::Bool],
        values: vec![
            ProjectionValue { declaration: member(1), definition: DefHash::new(13, 1), ty: Ty::uint(16) },
            ProjectionValue { declaration: member(2), definition: DefHash::new(13, 2), ty: Ty::Bool },
        ], span: SpanId(0),
    });
    source
}

#[test]
fn selected_implementation_member_and_all_ordered_arguments_define_one_type() {
    let source = source();
    let definitions = Definitions::checked(&source, &mut 100_000).unwrap();
    let formal = projection(1, vec![Ty::Param(0), Ty::Param(1)]);
    let arguments = [Ty::uint(8), Ty::Bool];
    assert_eq!(definitions.substitute(&formal, &arguments, &mut 100_000), Some(Ty::uint(16)));
    assert_eq!(definitions.equal_substitution(&formal, Some(&arguments), &Ty::uint(16), &mut 100_000), Some(true));
    assert_eq!(definitions.equal_substitution(&formal, Some(&arguments), &Ty::Bool, &mut 100_000), Some(false));
    assert_eq!(definitions.substitute(&projection(2, vec![Ty::Param(0), Ty::Param(1)]), &arguments, &mut 100_000), Some(Ty::Bool));
    assert_eq!(definitions.equal_substitution(&formal, Some(&[Ty::Bool, Ty::uint(8)]), &Ty::uint(16), &mut 100_000), Some(false));
    assert_eq!(definitions.equal_substitution(&formal, Some(&[Ty::uint(32), Ty::Bool]), &Ty::uint(16), &mut 100_000), Some(false));
    assert!(definitions.normalize(&projection(99, arguments.to_vec()), &mut 100_000).is_none());
}

#[test]
fn malformed_or_incomplete_implementations_provide_no_semantics() {
    for problem in 0..10 {
        let mut source = source();
        match problem {
            0 => source.projections[1].arity = 1,
            1 => { source.projection_impls[0].values.pop(); }
            2 => source.projection_impls[0].trait_id = DefHash::new(99, 0),
            3 => source.projection_impls[0].values[0].declaration = member(99),
            4 => source.projection_impls[0].arguments[0] = Ty::Param(0),
            5 => source.projection_impls[0].values[0].ty = projection(1, vec![Ty::uint(8), Ty::Bool]),
            6 => source.projection_impls[0].values[0].ty = projection(2, vec![Ty::uint(8), Ty::Bool]),
            7 => source.projection_impls[0].values[1].definition = source.projection_impls[0].values[0].definition,
            8 => { let repeated = source.projection_impls[0].clone(); source.projection_impls.push(repeated); }
            9 => { let mut competing = source.projection_impls[0].clone(); competing.id = DefHash::new(12, 2); source.projection_impls.push(competing); }
            _ => unreachable!(),
        }
        assert!(Definitions::checked(&source, &mut 100_000).is_none(), "malformed case {problem}");
    }
}

#[test]
fn normalization_prices_expanded_output_and_never_reinterprets_caller_parameters() {
    let source = source();
    let definitions = Definitions::checked(&source, &mut 100_000).unwrap();
    let formal = Ty::Tuple(vec![projection(1, vec![Ty::Param(0), Ty::Bool]); 8]);
    let mut work = 100_000;
    assert_eq!(definitions.substitute(&formal, &[Ty::uint(8)], &mut work), Some(Ty::Tuple(vec![Ty::uint(16); 8])));
    let cost = 100_000 - work;
    let mut one_short = cost - 1;
    assert!(definitions.substitute(&formal, &[Ty::uint(8)], &mut one_short).is_none());
    assert_eq!(one_short, 0);
    assert!(definitions.substitute(&Ty::Bool, &[], &mut one_short).is_none());
    assert_eq!(definitions.substitute(&Ty::Param(0), &[Ty::Param(1), Ty::Bool], &mut 100_000), Some(Ty::Param(1)));
}

#[test]
fn raw_datatype_fields_keep_associated_cycles_and_missing_edges_visible() {
    let id = AdtId(DefHash::new(20, 1));
    let datatype = Ty::Adt(id, vec![]);
    for shape in 0..3 {
        let mut source = source();
        source.projection_impls[0].arguments[0] = datatype.clone();
        let field = match shape {
            0 => Ty::Bool,
            1 => projection(1, vec![datatype.clone(), Ty::Bool]),
            2 => projection(1, vec![Ty::uint(32), Ty::Bool]),
            _ => unreachable!(),
        };
        source.adts.push(crate::AdtDecl {
            id, name: "S".into(), type_params: vec![], span: SpanId(0), kind: crate::AdtKind::Struct,
            variants: vec![crate::VariantDecl { name: "S".into(), fields: vec![crate::FieldDecl {
                name: "field".into(), ty: field, mode: crate::Mode::Exec,
            }] }],
        });
        assert_eq!(Definitions::checked(&source, &mut 100_000).is_some(), shape == 0, "shape {shape}");
    }
}
