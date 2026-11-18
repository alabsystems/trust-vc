//! Native eligibility for the built-in copy-body Clone derive.
//!
//! Eligibility registers a real function; it does not verify it. Its complete
//! original body and the derived identity postcondition use the normal pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

extern crate rustc_abi;

use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::{
    self as hir,
    def::Res,
    def::{DefKind, MacroKinds},
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypeckResults};
use rustc_span::Symbol;

use super::{attrs, is_external, Cx, Refusal};

/// A native call selection, not a verified body, mode packet or permission.
/// Only the complete ordinary mode walk retains it for body lowering.
#[derive(Clone)]
pub(super) struct Call<'tcx> {
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    expression: &'tcx hir::Expr<'tcx>,
    pub(super) original: DefId,
    pub(super) original_args: ty::GenericArgs<'tcx>,
    pub(super) method: LocalDefId,
    pub(super) args: ty::GenericArgs<'tcx>,
}

impl std::fmt::Debug for Call<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DerivedCloneCall")
            .field("caller", &self.caller)
            .field("expression", &self.expression.hir_id)
            .field("method", &self.method)
            .finish_non_exhaustive()
    }
}

impl Call<'_> {
    pub(super) fn same_selection(&self, other: &Self) -> bool {
        std::ptr::eq(*self.tcx, *other.tcx)
            && self.caller == other.caller
            && std::ptr::eq(self.body, other.body)
            && std::ptr::eq(self.typeck, other.typeck)
            && std::ptr::eq(self.expression, other.expression)
            && self.original == other.original
            && self.original_args == other.original_args
            && self.method == other.method
            && self.args == other.args
    }
}

#[derive(Default)]
pub(super) struct Registry {
    /// Actual generated method -> (actual impl, actual enum).
    methods: HashMap<LocalDefId, (LocalDefId, LocalDefId)>,
}

impl Registry {
    /// Resolve only the actual core trait call to an already authenticated
    /// local copy-body derive. Ordinary foreign/trait dispatch stays closed.
    pub(super) fn call<'tcx>(
        &self,
        cx: &Cx<'tcx>,
        caller: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Result<Option<Call<'tcx>>, Refusal> {
        let tcx = cx.tcx;
        // A missing product/source join supplies no selection. In particular,
        // do not query a caller-asserted TypeckResults with another body's ID.
        // Ordinary calls keep their existing independent source checks.
        if self.methods.is_empty()
            || tcx.dcx().has_errors().is_some()
            || super::function_identity_observer::body_is_quarantined(tcx.sess, caller)
        {
            return Ok(None);
        }
        let Some(body) = tcx.hir_maybe_body_owned_by(caller) else {
            return Ok(None);
        };
        if expression.hir_id.owner.def_id != caller
            || !std::ptr::eq(typeck, tcx.typeck(caller))
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Ok(None);
        }
        let native_owner = tcx.hir_enclosing_body_owner(expression.hir_id);
        if super::function_identity_observer::body_is_quarantined(tcx.sess, native_owner) {
            return Ok(None);
        }
        let (original, original_args) = match expression.kind {
            hir::ExprKind::MethodCall(..) => {
                let Some(def) = typeck.type_dependent_def_id(expression.hir_id) else {
                    return Ok(None);
                };
                (def, typeck.node_args(expression.hir_id))
            }
            hir::ExprKind::Call(function, _) => {
                let hir::ExprKind::Path(ref path) = function.kind else {
                    return Ok(None);
                };
                let Res::Def(DefKind::AssocFn, def) = typeck.qpath_res(path, function.hir_id)
                else {
                    return Ok(None);
                };
                (def, typeck.node_args(function.hir_id))
            }
            _ => return Ok(None),
        };
        let Some(clone_trait) = tcx.get_diagnostic_item(Symbol::intern("Clone")) else {
            return Ok(None);
        };
        if tcx.trait_of_assoc(original) != Some(clone_trait) {
            return Ok(None);
        }
        let Some(self_ty) = original_args.types().next() else {
            return Ok(None);
        };
        let ty::Adt(adt, enum_args) = self_ty.kind() else {
            return Ok(None);
        };
        let Some((&method, &(implementation, enumeration))) = self
            .methods
            .iter()
            .find(|(_, (_, enumeration))| enumeration.to_def_id() == adt.did())
        else {
            return Ok(None);
        };
        // The exact associated-item link distinguishes clone from clone_from
        // without accepting another function because its name is spelled alike.
        if tcx.associated_item(method).trait_item_def_id() != Some(original) {
            return Ok(None);
        }
        let refuse = |reason: &str| Refusal::new("derived-clone-call", reason, expression.span);
        let ready = || {
            tcx.dcx().has_errors().is_none()
                && expression.hir_id.owner.def_id == caller
                && std::ptr::eq(typeck, tcx.typeck(caller))
                && matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
                && tcx
                    .hir_maybe_body_owned_by(caller)
                    .is_some_and(|actual| std::ptr::eq(actual, body))
                && !super::function_identity_observer::body_is_quarantined(tcx.sess, caller)
                && !super::function_identity_observer::body_is_quarantined(tcx.sess, native_owner)
                && !super::function_identity_observer::body_is_quarantined(tcx.sess, method)
                && !super::function_identity_observer::body_is_quarantined(tcx.sess, implementation)
                && !super::function_identity_observer::body_is_quarantined(tcx.sess, enumeration)
        };
        if !ready()
            || !self.admitted(cx, method)
            || is_external(tcx, method)
            || is_external(tcx, implementation)
            || !enum_args.is_empty()
            || original_args.len() != 1
            || original_args.has_param()
            || original_args.has_infer()
            || original_args.has_placeholders()
            || original_args.has_opaque_types()
            || original_args.has_escaping_bound_vars()
            || original_args.references_error()
            || !tcx.check_args_compatible(original, original_args)
        {
            return Err(refuse(
                "the original native call or local enum is not current and closed",
            ));
        }
        // Keep the original Self argument's translation, bounds and WF checks;
        // the selected nongeneric method's empty args cannot stand in for them.
        let env = native_owner.to_def_id();
        for argument in original_args.iter() {
            if cx.verus_arg_problem(argument, env)?.is_some() {
                return Err(refuse(
                    "the original Self argument is outside Verus translation",
                ));
            }
        }
        if cx
            .verus_bounds_problem(original, original_args, env)?
            .is_some()
            || cx.verus_wf_problem(self_ty, env)?.is_some()
        {
            return Err(refuse(
                "the original native call's bounds or Self well-formedness are unsupported",
            ));
        }
        let typing_env = ty::TypingEnv::post_typeck_through_borrowck(tcx, native_owner);
        let Some(instance) = ty::Instance::try_resolve(tcx, typing_env, original, original_args)
            .map_err(|_| refuse("native Clone call selection failed"))?
        else {
            return Err(refuse("native Clone call selection is not determined"));
        };
        if !matches!(instance.def, ty::InstanceKind::Item(def) if def == method.to_def_id())
            || !instance.args.is_empty()
            || tcx.local_parent(method) != implementation
            || tcx
                .impl_trait_ref(implementation)
                .instantiate_identity()
                .skip_normalization()
                .def_id
                != clone_trait
            || tcx
                .type_of(implementation)
                .instantiate_identity()
                .skip_normalization()
                != self_ty
            || !cx.fns.contains_key(&method.to_def_id())
        {
            return Err(refuse(
                "native selection is not this registered local Clone body",
            ));
        }
        let item = cx.declaration_attrs(method);
        if item.external
            || item.external_body
            || item.uninterp
            || item.opaque
            || !item.unsupported.is_empty()
        {
            return Err(refuse(
                "the selected local Clone declaration cannot supply an ordinary body",
            ));
        }
        let signature = tcx.liberate_late_bound_regions(
            method.to_def_id(),
            tcx.fn_sig(method)
                .instantiate(tcx, instance.args)
                .skip_normalization(),
        );
        let original_signature = tcx.liberate_late_bound_regions(
            original,
            tcx.fn_sig(original)
                .instantiate(tcx, original_args)
                .skip_normalization(),
        );
        if signature.safety().is_unsafe()
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != 1
            || signature.output() != self_ty
            || !matches!(signature.inputs()[0].kind(), ty::Ref(_, inner, Mutability::Not) if *inner == self_ty)
            || tcx.erase_and_anonymize_regions(signature)
                != tcx.erase_and_anonymize_regions(original_signature)
            || !ready()
        {
            return Err(refuse(
                "the selected native Clone signature or source changed",
            ));
        }
        Ok(Some(Call {
            tcx,
            caller,
            body,
            typeck,
            expression,
            original,
            original_args,
            method,
            args: instance.args,
        }))
    }

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
