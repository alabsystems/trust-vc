// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Distinguish checked-source refusal from the documented unverified boundary.

use super::*;
use rustc_middle::ty;

#[test]
fn native_drop_bodies_preserve_runtime_reference_and_external_boundaries() {
    native::run_with_options(
        r#"
#[verus::internal(verus_macro)]
struct NativeCarrier {}
#[verus::internal(verus_macro)]
impl Drop for NativeCarrier {
    #[verus::internal(verus_macro)]
    fn drop(&mut self) {
        unwind_builtin_fixture::opens_invariants_none();
        unwind_builtin_fixture::no_unwind();
    }
}
#[verus::internal(verus_macro)]
struct ExternalCarrier {}
impl Drop for ExternalCarrier { fn drop(&mut self) {} }
"#,
        |tcx, read| {
            let drop_trait = tcx
                .lang_items()
                .drop_trait()
                .expect("the real Drop language item exists");
            let actual = read
                .fns
                .iter()
                .filter_map(|record| {
                    let implementation = tcx.trait_impl_of_assoc(record.def_id.to_def_id())?;
                    if tcx.impl_trait_id(implementation) != drop_trait {
                        return None;
                    }
                    let environment = ty::TypingEnv::non_body_analysis(tcx, implementation);
                    let self_ty = tcx
                        .try_normalize_erasing_regions(
                            environment,
                            tcx.type_of(implementation).instantiate_identity(),
                        )
                        .expect("the actual Drop implementation Self type normalizes");
                    let ty::Adt(definition, _) = self_ty.kind() else {
                        panic!("the actual Drop receiver has its native ADT");
                    };
                    Some((tcx.item_name(definition.did()).to_string(), record))
                })
                .collect::<Vec<_>>();
            assert_eq!(
                actual.len(),
                2,
                "both real Drop implementations are observed: {actual:?}"
            );
            let native = actual
                .iter()
                .find(|(name, _)| name == "NativeCarrier")
                .unwrap()
                .1;
            let external = actual
                .iter()
                .find(|(name, _)| name == "ExternalCarrier")
                .unwrap()
                .1;
            assert_ne!(native.def_id, external.def_id);
            assert!(
                matches!(&native.status, crate::reader::FnStatus::Refused(refusal)
            if refusal.tag == "new-mut-ref"),
                "{:?}",
                native.status
            );
            assert!(
                matches!(external.status, crate::reader::FnStatus::External),
                "{:?}",
                external.status
            );
            let native_id = read
                .fn_defs
                .iter()
                .find_map(|(id, definition)| (*definition == native.def_id).then_some(*id))
                .expect("the requested native Drop was actually registered");
            assert!(
                read.fn_defs
                    .values()
                    .all(|definition| *definition != external.def_id),
                "an unmarked external Drop must not be registered for verification"
            );
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            assert!(read.krate.fn_decl(native_id).is_none());
            assert!(generated.get(native_id).is_none());
            for record in [native, external] {
                assert!(!read.native_ownership.contains(&record.def_id));
                assert!(!read.ghost_ownership.contains_key(&record.def_id));
                for (id, definition) in &read.fn_defs {
                    if *definition == record.def_id {
                        assert!(read.krate.fn_decl(*id).is_none());
                        assert!(
                            generated.get(*id).is_none(),
                            "a refused/external Drop must not become Checks([])"
                        );
                    }
                }
                assert!(read
                    .krate
                    .fns
                    .iter()
                    .all(|declaration| read.fn_defs.get(&declaration.id) != Some(&record.def_id)));
            }
        },
        ReadOptions {
            new_mut_ref: true,
            ..ReadOptions::default()
        },
    );
}
