// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Contracts are inherited from the real trait declaration, with substitution.

use super::*;

#[test]
fn native_unwind_trait_conditions_use_original_parameters_and_substitution() {
    native::run(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verus::internal(open)]
pub fn Predicate<A>(_value: A, enabled: bool) -> bool { enabled }
#[verus::internal(verus_macro)]
trait Contract<A> {
    #[verus::internal(verus_macro)]
    fn perform(value: A, enabled: bool);
    #[verus::internal(verus_macro)]
    fn VERUS_SPEC__perform(original: A, condition: bool) {
        unwind_builtin_fixture::no_unwind_when(Predicate(original, condition));
        unwind_builtin_fixture::no_method_body()
    }
}
#[verus::internal(verus_macro)]
struct Receiver {}
#[verus::internal(verus_macro)]
impl Contract<u64> for Receiver {
    #[verus::internal(verus_macro)]
    fn perform(renamed_value: u64, renamed_condition: bool) {}
}
#[verus::internal(verus_macro)]
fn Invoke() { <Receiver as Contract<u64>>::perform(4u64, true); }
"#,
        |tcx, read| {
            clean(read);
            let declarations = read
                .krate
                .fns
                .iter()
                .filter(|decl| decl.name.ends_with("perform") && decl.role != FnRole::Instance)
                .collect::<Vec<_>>();
            assert_eq!(declarations.len(), 2, "{declarations:?}");
            let source = declarations
                .iter()
                .find(|decl| decl.role == FnRole::TraitDecl)
                .unwrap();
            let implementation = declarations
                .iter()
                .find(|decl| decl.role == FnRole::Item)
                .unwrap();
            assert!(matches!(source.body, Body::None));
            assert!(matches!(implementation.body, Body::Stmts(_)));
            for declaration in [*source, *implementation] {
                let condition = declaration.unwind.as_ref().unwrap().condition().unwrap();
                let ExprKind::Call { args, .. } = &condition.kind else {
                    panic!("the original typed predicate call is retained");
                };
                assert_eq!(args.len(), 2);
                for (argument, parameter) in args.iter().zip(&declaration.params) {
                    assert!(
                        matches!(&argument.kind, ExprKind::Read(place) if place.local == *parameter
                    && place.projections.is_empty()),
                        "{declaration:?}"
                    );
                }
                if declaration.role == FnRole::Item {
                    assert_eq!(args[0].ty, trust_vc_vcir::Ty::uint(64));
                    assert_eq!(
                        declaration.locals[declaration.params[0].index()].name,
                        "renamed_value"
                    );
                    assert_eq!(
                        declaration.locals[declaration.params[1].index()].name,
                        "renamed_condition"
                    );
                } else {
                    assert!(matches!(args[0].ty, trust_vc_vcir::Ty::Param(_)));
                }
            }
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            assert!(matches!(
                generated.get(function(tcx, read, "Invoke").id),
                Some(trust_vc_vcir::vcgen::FnVcs::Checks(_))
            ));
        },
    );
}

#[test]
fn native_unwind_trait_implementation_cannot_replace_the_declared_contract() {
    native::run(
        r#"
#[verus::internal(verus_macro)]
trait Contract {
    #[verus::internal(verus_macro)]
    fn perform();
    #[verus::internal(verus_macro)]
    fn VERUS_SPEC__perform() { unwind_builtin_fixture::no_unwind(); unwind_builtin_fixture::no_method_body() }
}
#[verus::internal(verus_macro)]
struct Receiver {}
#[verus::internal(verus_macro)]
impl Contract for Receiver {
    #[verus::internal(verus_macro)]
    fn perform() { unwind_builtin_fixture::no_unwind_when(true); }
}
"#,
        |_, read| {
            assert!(
                read.errors
                    .iter()
                    .any(|error| error.message == crate::messages::traits::IMPL_UNWIND),
                "the local implementation must not substitute its own contract: {:?}",
                read.errors
            );
        },
    );
}
