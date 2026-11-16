// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual native lowering freezes earlier constructor values before effects.

use super::*;

#[test]
fn native_constructor_transport_freezes_plain_fields_in_source_order() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Plain { first: u64, second: u64 }
#[verus::internal(verus_macro)] struct Pair(u64, u64);
#[verus::internal(verus_macro)]
fn Record(mut value: u64) -> Plain { Plain { second: value, first: { value = 7; value } } }
#[verus::internal(verus_macro)]
fn Tuple(mut value: u64) -> Pair { Pair(value, { value = 9; value }) }
"#,
        |tcx, read| {
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            assert!(
                read.refusals().next().is_none(),
                "{:?}",
                read.refusals().collect::<Vec<_>>()
            );
            assert!(
                read.verify_refusals.is_empty(),
                "{:?}",
                read.verify_refusals
            );
            assert!(trust_vc_vcir::wf::check_crate(&read.krate).is_empty());
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            for adt in &read.krate.adts {
                assert!(adt
                    .variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .all(|field| field.mode == Mode::Exec));
            }
            for (name, saved_field) in [("Record", 1), ("Tuple", 0)] {
                let owner = named(tcx, name);
                let function = read
                    .krate
                    .fns
                    .iter()
                    .find(|function| read.fn_defs.get(&function.id) == Some(&owner))
                    .unwrap();
                assert_eq!(function.role, trust_vc_vcir::FnRole::Item);
                assert!(
                    matches!(
                        generated.get(function.id),
                        Some(trust_vc_vcir::vcgen::FnVcs::Checks(_))
                    ),
                    "{name}: {generated:?}"
                );
                let Body::Stmts(block) = &function.body else {
                    panic!("actual constructor body statements");
                };
                let parameter = function.params[0];
                let saved: Vec<_> = block.stmts.iter().enumerate().filter_map(|(position, stmt)| {
                let StmtKind::Let { local, init: Some(value) } = &stmt.kind else { return None; };
                matches!(&value.kind, ExprKind::Read(place) if place.local == parameter && place.projections.is_empty())
                    .then_some((position, *local))
            }).collect();
                assert_eq!(saved.len(), 1, "{name}: {block:?}");
                let (saved_at, local) = saved[0];
                assert_eq!(function.locals[local.index()].kind, LocalKind::Temp);
                assert_eq!(function.locals[local.index()].mode, Mode::Exec);
                let assigned_at = block.stmts.iter().position(|stmt| matches!(&stmt.kind, StmtKind::Assign { place, .. } if place.local == parameter)).unwrap();
                assert!(saved_at < assigned_at, "{name}");
                let fields = block
                    .stmts
                    .iter()
                    .find_map(|stmt| match &stmt.kind {
                        StmtKind::Return {
                            value: Some(value), ..
                        } => match &value.kind {
                            ExprKind::Ctor { fields, .. } => Some(fields),
                            _ => None,
                        },
                        _ => None,
                    })
                    .unwrap();
                assert!(
                    matches!(&fields[saved_field].kind, ExprKind::Read(place) if place.local == local)
                );
                assert!(
                    matches!(&fields[1 - saved_field].kind, ExprKind::Read(place) if place.local == parameter)
                );
            }
        },
        false,
    );
}
