//! Native eligibility for the built-in copy-body Clone derive.
//!
//! Eligibility registers a real function; it does not verify it. Its complete
//! original body and the derived identity postcondition use the normal pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::{
    self as hir,
    def::Res,
    def::{DefKind, MacroKinds},
    def_id::LocalDefId,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;

use super::{attrs, is_external, Cx};

#[derive(Default)]
pub(super) struct Registry {
    /// Actual generated method -> (actual impl, actual enum).
    methods: HashMap<LocalDefId, (LocalDefId, LocalDefId)>,
}

impl Registry {
    pub(super) fn collect(tcx: TyCtxt<'_>, loose: bool) -> Self {
        let mut out = Self::default();
        let Some(clone_trait) = tcx.get_diagnostic_item(Symbol::intern("Clone")) else {
            return out;
        };
        // Resolve the macro namespace in the actual trait's defining module.
        // A reexport, a user macro named Clone, or another builtin derive is
        // not this definition. The privileged builtin attribute is checked
        // separately by is_builtin_derived on each actual expansion below.
        let mut macros = tcx
            .module_children(tcx.parent(clone_trait))
            .iter()
            .filter_map(|child| {
                if child.ident.name == tcx.item_name(clone_trait) {
                    if let Res::Def(DefKind::Macro(MacroKinds::DERIVE), definition) = child.res {
                        return Some(definition);
                    }
                }
                None
            });
        let Some(clone_macro) = macros.next() else {
            return out;
        };
        if macros.next().is_some() || clone_macro.krate != clone_trait.krate {
            return out;
        }
        for owner in tcx.hir_crate_items(()).owners() {
            let implementation = owner.def_id;
            if !matches!(
                tcx.def_kind(implementation),
                DefKind::Impl { of_trait: true }
            ) || !tcx.is_builtin_derived(implementation.to_def_id())
                || is_external(tcx, implementation)
            {
                continue;
            }
            let expansion = tcx.def_span(implementation).ctxt().outer_expn_data();
            // is_builtin_derived checks the privileged RustcBuiltinMacro
            // definition attribute, not the user-spellable derived marker or
            // expansion name. Join that definition to the real core Clone.
            if expansion.macro_def_id != Some(clone_macro)
                || tcx
                    .impl_trait_ref(implementation)
                    .instantiate_identity()
                    .skip_normalization()
                    .def_id
                    != clone_trait
                || !tcx.generics_of(implementation).own_params.is_empty()
            {
                continue;
            }
            let native = tcx
                .type_of(implementation)
                .instantiate_identity()
                .skip_normalization();
            let ty::Adt(adt, args) = native.kind() else {
                continue;
            };
            let Some(enumeration) = adt.did().as_local() else {
                continue;
            };
            if !adt.is_enum()
                || !args.is_empty()
                || adt.variants().is_empty()
                || adt.variants().iter().any(|v| !v.fields.is_empty())
                || is_external(tcx, enumeration)
                || !(loose
                    || attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(enumeration)))
                        .verus_macro)
            {
                continue;
            }
            let [method] = tcx.associated_item_def_ids(implementation) else {
                continue;
            };
            let Some(method) = method.as_local() else {
                continue;
            };
            if tcx.def_kind(method) != DefKind::AssocFn
                || tcx.local_parent(method) != implementation
                || tcx.def_span(method).ctxt() != tcx.def_span(implementation).ctxt()
                || !tcx.generics_of(method).own_params.is_empty()
            {
                continue;
            }
            let signature = tcx.liberate_late_bound_regions(
                method.to_def_id(),
                tcx.fn_sig(method)
                    .instantiate_identity()
                    .skip_normalization(),
            );
            if signature.inputs().len() != 1
                || signature.output() != native
                || !matches!(signature.inputs()[0].kind(), ty::Ref(_, inner, Mutability::Not) if *inner == native)
            {
                continue;
            }
            let Some(body) = tcx.hir_maybe_body_owned_by(method) else {
                continue;
            };
            let [parameter] = body.params else { continue };
            let hir::PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), binding, _, None) =
                parameter.pat.kind
            else {
                continue;
            };
            let hir::ExprKind::Block(block, None) = body.value.kind else {
                continue;
            };
            if !block.stmts.is_empty() {
                continue;
            }
            let Some(value) = block.expr else { continue };
            let hir::ExprKind::Unary(hir::UnOp::Deref, operand) = value.kind else {
                continue;
            };
            let hir::ExprKind::Path(ref path) = operand.kind else {
                continue;
            };
            let typeck = tcx.typeck(method);
            if typeck.qpath_res(path, operand.hir_id) != Res::Local(binding)
                || typeck.expr_ty(value) != native
                // Body typeck deliberately erases regions; join its actual
                // parameter binding to its actual use, rather than comparing
                // erased expression regions with FnSig's bound regions.
                || typeck.pat_ty(parameter.pat) != typeck.expr_ty(operand)
                || !matches!(typeck.expr_ty(operand).kind(), ty::Ref(_, inner, Mutability::Not) if *inner == native)
            {
                continue;
            }
            out.methods.insert(method, (implementation, enumeration));
        }
        out
    }

    pub(super) fn source(&self, definition: LocalDefId) -> Option<LocalDefId> {
        self.methods
            .get(&definition)
            .map(|(_, enumeration)| *enumeration)
    }

    pub(super) fn implementation(&self, definition: LocalDefId) -> bool {
        self.methods
            .values()
            .any(|(implementation, _)| *implementation == definition)
    }

    pub(super) fn admitted(&self, cx: &Cx<'_>, method: LocalDefId) -> bool {
        self.source(method).is_some_and(|enumeration| {
            cx.adt_id(enumeration.to_def_id()).is_some()
                && !cx.source_opaque_nominal(enumeration.to_def_id())
                && cx.imported_nominal(enumeration.to_def_id()).is_none()
        })
    }
}
