// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordinary compiler controls for declaration and original-binding modes.
//! These observations supply no SDK, import or availability capability.

use super::*;
use crate::reader::declaration_modes::DeclarationModes;
use crate::reader::modes::{self, ModeContext};
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::{self, Visitor};
use trust_vc_vcir::{Body, ExprKind, LocalKind, StmtKind};

mod constructors;
mod declarations;
mod inference;

struct Context<'tcx>(DeclarationModes<'tcx>);

impl<'tcx> ModeContext<'tcx> for Context<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx()
    }
    fn function_mode(&self, def: DefId) -> Option<Mode> {
        self.0.function_mode(def)
    }
    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.0.body_owner(def)
    }
    fn declaration_attrs(&self, def: LocalDefId) -> crate::reader::attrs::ItemAttrs {
        self.0.declaration_attrs(def)
    }
    fn verus_item(&self, def: DefId) -> Option<crate::verus_items::VerusItem> {
        self.0.verus_item(def)
    }
    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.0.constant_proxy(def)
    }
    fn constant_mode(&self, def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.0.constant_mode(def)
    }
    fn friendly_fn_path(&self, def: DefId) -> String {
        self.0.friendly_fn_path(def)
    }
    fn read_adt_field_modes(&self) -> bool {
        true
    }
    fn permits_adt_fields(&self, def: DefId) -> bool {
        def.is_local()
    }
}

fn checked<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> modes::CheckedModes<'tcx> {
    let context = Context(DeclarationModes::new(tcx));
    match modes::check_with_context(&context, named(tcx, name)) {
        modes::ModeCheck::Clean(facts) => facts,
        result => panic!("the actual whole-body mode walk for {name} must complete: {result:?}"),
    }
}

fn binding<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, name: &str) -> &'tcx hir::Pat<'tcx> {
    struct Find<'a, 'tcx> {
        name: &'a str,
        found: Vec<&'tcx hir::Pat<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
            if matches!(pat.kind, hir::PatKind::Binding(_, _, ident, _) if ident.name.as_str() == self.name)
            {
                self.found.push(pat);
            }
            intravisit::walk_pat(self, pat);
        }
    }
    let mut visitor = Find {
        name,
        found: Vec::new(),
    };
    visitor.visit_body(tcx.hir_body_owned_by(owner));
    assert_eq!(visitor.found.len(), 1, "actual binding {name}");
    visitor.found[0]
}

#[test]
fn native_nested_binding_modes_require_original_patterns_and_body() {
    native(
        r#"
#[verus::internal(verus_macro)]
struct Mixed<T> { live: T, #[verus::internal(spec)] snapshot: T, #[verus::internal(proof)] token: u64 }
#[verus::internal(verus_macro)]
struct Triple<T>(T, #[verus::internal(spec)] T, #[verus::internal(proof)] u64);
#[verus::internal(verus_macro)]
fn Nested<T>(value: (Mixed<T>, u64)) {
    let (Mixed { live, snapshot, token }, last) = value;
    #[verus::internal(infer_mode)] let pending: u64;
}
#[verus::internal(verus_macro)]
fn TupleNested<T>(value: (Triple<T>, u64)) {
    let (Triple(live, snapshot, token), last) = value;
}
#[verus::internal(verus_macro)]
fn Infer(value: u64) { #[verus::internal(infer_mode)] let assigned; assigned = value; }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Pure(value: (Mixed<u64>, u64)) -> u64 {
    let (Mixed { live, snapshot, token }, last) = value;
    live
}
#[verus::internal(verus_macro)] fn Other(value: u64) { let local = value; }
"#,
        |tcx, read| {
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            let owner = named(tcx, "Nested");
            let body = tcx.hir_body_owned_by(owner);
            let facts = checked(tcx, "Nested");
            for (name, expected) in [
                ("value", Mode::Exec),
                ("live", Mode::Exec),
                ("snapshot", Mode::Spec),
                ("token", Mode::Proof),
                ("last", Mode::Exec),
            ] {
                let pat = binding(tcx, owner, name);
                assert_eq!(
                    facts
                        .bindings
                        .mode_for(tcx, owner, owner, body, pat)
                        .unwrap(),
                    expected,
                    "{name}"
                );
            }
            let original = binding(tcx, owner, "snapshot");
            let copied = *original;
            assert!(facts
                .bindings
                .mode_for(tcx, owner, owner, body, &copied)
                .is_err());
            let copied_body = *body;
            assert!(facts
                .bindings
                .mode_for(tcx, owner, owner, &copied_body, original)
                .is_err());
            let other = named(tcx, "Other");
            assert!(facts
                .bindings
                .mode_for(tcx, other, owner, body, original)
                .is_err());
            assert!(facts
                .bindings
                .mode_for(tcx, owner, other, body, original)
                .is_err());
            assert!(facts
                .bindings
                .mode_for(tcx, owner, owner, body, binding(tcx, other, "local"))
                .is_err());
            assert!(facts
                .bindings
                .mode_for(tcx, owner, owner, body, binding(tcx, owner, "pending"))
                .is_err());
            let tuple = named(tcx, "TupleNested");
            let tuple_facts = checked(tcx, "TupleNested");
            for (name, expected) in [
                ("live", Mode::Exec),
                ("snapshot", Mode::Spec),
                ("token", Mode::Proof),
                ("last", Mode::Exec),
            ] {
                assert_eq!(
                    tuple_facts
                        .bindings
                        .mode_for(
                            tcx,
                            tuple,
                            tuple,
                            tcx.hir_body_owned_by(tuple),
                            binding(tcx, tuple, name)
                        )
                        .unwrap(),
                    expected,
                    "{name}"
                );
            }
            let inferred = named(tcx, "Infer");
            assert_eq!(
                checked(tcx, "Infer")
                    .bindings
                    .mode_for(
                        tcx,
                        inferred,
                        inferred,
                        tcx.hir_body_owned_by(inferred),
                        binding(tcx, inferred, "assigned")
                    )
                    .unwrap(),
                Mode::Exec
            );
            let pure = named(tcx, "Pure");
            let facts = checked(tcx, "Pure");
            for name in ["live", "snapshot", "token", "last"] {
                assert_eq!(
                    facts
                        .bindings
                        .mode_for(
                            tcx,
                            pure,
                            pure,
                            tcx.hir_body_owned_by(pure),
                            binding(tcx, pure, name)
                        )
                        .unwrap(),
                    Mode::Spec
                );
            }
            assert!(read
                .item_refusals
                .iter()
                .any(|refusal| refusal.tag == "field-mode"));
            assert!(read.native_ownership.is_empty());
        },
        false,
    );
}
