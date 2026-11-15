// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The actual original native imported-call census, never an import constructor.

use std::collections::HashMap;

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    self as hir,
    def::Res,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use serde_json::{json, Value};
use trust_vc_vcir::{FnDecl, FnId};

use super::{key, vcir::Budget};
use crate::declaration_alignment::source_bindings::PinnedFile;
use crate::reader::{declaration_facts, declaration_types};

pub(super) struct Source<'a> {
    pub(super) file: &'a PinnedFile,
    pub(super) bytes: &'a [u8],
}

impl Source<'_> {
    pub(super) fn anchor(
        &self,
        tcx: TyCtxt<'_>,
        span: Span,
        budget: &mut Budget,
    ) -> Result<Value, String> {
        use rustc_span::{SourceFileHash, SourceFileHashAlgorithm};
        budget.charge(1, self.bytes.len(), 0)?;
        let value = declaration_facts::source_anchor(tcx, span.source_callsite());
        if value["state"] != "ObservedRealSourceAnchor" {
            return Err("client footprint has no real original source anchor".into());
        }
        let path = std::path::Path::new(
            value["local_path"]
                .as_str()
                .ok_or("native source path is unavailable")?,
        )
        .canonicalize()
        .map_err(|e| e.to_string())?;
        let hash = value["compiler_source_hash"]
            .as_str()
            .ok_or("native source hash is unavailable")?;
        let kind: SourceFileHashAlgorithm = hash
            .split_once('=')
            .ok_or("native source hash kind is unavailable")?
            .0
            .parse()
            .map_err(|()| "native source hash kind is unsupported")?;
        if path != self.file.path
            || SourceFileHash::new_in_memory(kind, self.bytes).to_string() != hash
            || value["original_file_len"].as_u64() != Some(self.bytes.len() as u64)
        {
            return Err(
                "the native footprint source differs from the actual unchanged client bytes".into(),
            );
        }
        Ok(value)
    }
}

fn native_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ty::Ty<'tcx>,
    budget: &mut Budget,
    depth: usize,
) -> Result<Value, String> {
    budget.charge(1, 96, depth)?;
    Ok(match value.kind() {
        ty::Bool => json!({"kind": "Bool"}),
        ty::Int(kind) => json!({"kind": "SignedInteger", "width": match kind {
            ty::IntTy::I8 => "8", ty::IntTy::I16 => "16", ty::IntTy::I32 => "32",
            ty::IntTy::I64 => "64", ty::IntTy::I128 => "128", ty::IntTy::Isize => "pointer" }}),
        ty::Uint(kind) => json!({"kind": "UnsignedInteger", "width": match kind {
            ty::UintTy::U8 => "8", ty::UintTy::U16 => "16", ty::UintTy::U32 => "32",
            ty::UintTy::U64 => "64", ty::UintTy::U128 => "128", ty::UintTy::Usize => "pointer" }}),
        ty::Param(parameter) => json!({"kind": "Parameter", "index": parameter.index}),
        ty::Tuple(values) => {
            budget.charge(values.len(), 0, depth)?;
            json!({"kind": "Tuple", "elements": values.iter().map(|value|
                native_type(tcx, value, budget, depth + 1)).collect::<Result<Vec<_>, _>>()?})
        }
        ty::Ref(_, inner, mutable) => json!({"kind": "Reference", "mutable": mutable.is_mut(),
            "region_authority": "Unknown; observation erases regions",
            "inner": native_type(tcx, *inner, budget, depth + 1)?}),
        ty::Adt(adt, arguments) => {
            budget.charge(arguments.len(), 0, depth)?;
            let arguments = arguments
                .iter()
                .map(|argument| match argument.kind() {
                    ty::GenericArgKind::Type(value) => native_type(tcx, value, budget, depth + 1),
                    _ => Err(
                        "client footprint has an unrepresented native lifetime/const argument"
                            .into(),
                    ),
                })
                .collect::<Result<Vec<_>, _>>()?;
            json!({"kind": "Nominal", "definition": key(tcx, adt.did()), "arguments": arguments})
        }
        _ => return Err("client footprint has an unrepresented native type".into()),
    })
}

pub(super) fn signature(
    tcx: TyCtxt<'_>,
    definition: DefId,
    budget: &mut Budget,
) -> Result<Value, String> {
    let signature = declaration_types::signature(tcx, definition);
    if signature["state"] != "ObservedStructuralSignature" {
        return Err("the native declaration signature is unrepresented".into());
    }
    let encoded = serde_json::to_vec(&signature).map_err(|e| e.to_string())?;
    budget.charge(0, encoded.len(), 0)?;
    Ok(signature)
}

pub(super) struct Call {
    pub(super) definition: DefId,
    pub(super) callee: FnId,
    pub(super) span: Span,
    pub(super) type_argument_count: usize,
    pub(super) value_argument_count: usize,
    pub(super) value: Value,
}

pub(super) struct Assertion {
    pub(super) span: Span,
    pub(super) value: Value,
}

pub(super) struct Report {
    pub(super) calls: Vec<Call>,
    pub(super) assertions: Vec<Assertion>,
}

pub(super) fn parameters(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    decl: &FnDecl,
    budget: &mut Budget,
) -> Result<Value, String> {
    let body = tcx
        .hir_maybe_body_owned_by(owner)
        .ok_or("local footprint function has no native body")?;
    budget.charge(body.params.len(), 0, 0)?;
    if body.params.len() != decl.params.len() {
        return Err("native and VcIR parameter inventories differ".into());
    }
    let mut parameters = Vec::new();
    for (native, local) in body.params.iter().zip(&decl.params) {
        let hir::PatKind::Binding(_, binding, _, None) = native.pat.kind else {
            return Err("native footprint parameter pattern is unrepresented".into());
        };
        parameters.push(json!({"vcir_local": local.0, "native_binding_owner": key(tcx, binding.owner.def_id.to_def_id()),
            "native_binding_local": binding.local_id.as_u32(),
            "native_type": native_type(tcx, tcx.typeck(owner).pat_ty(native.pat), budget, 0)?}));
    }
    Ok(json!(parameters))
}

struct Walk<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    imported: &'a HashMap<DefId, FnId>,
    source: &'a Source<'a>,
    assertion_definition: Option<DefId>,
    budget: &'a mut Budget,
    calls: Vec<Call>,
    assertions: Vec<Assertion>,
    error: Option<String>,
    depth: usize,
}

impl<'tcx> Walk<'_, 'tcx> {
    fn call(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Result<(), String> {
        let typeck = self.tcx.typeck(self.owner);
        let (definition, arguments, generic_node) = match expr.kind {
            hir::ExprKind::MethodCall(_, receiver, args, _) => {
                let Some(definition) = typeck.type_dependent_def_id(expr.hir_id) else {
                    return Err("native footprint method has no resolved declaration".into());
                };
                self.budget.charge(args.len() + 1, 0, self.depth)?;
                (
                    definition,
                    std::iter::once(receiver).chain(args).collect::<Vec<_>>(),
                    expr.hir_id,
                )
            }
            hir::ExprKind::Call(callee, args) => {
                let hir::ExprKind::Path(ref path) = callee.kind else {
                    return Ok(());
                };
                let Res::Def(_, definition) = typeck.qpath_res(path, callee.hir_id) else {
                    return Ok(());
                };
                self.budget.charge(args.len(), 0, self.depth)?;
                (definition, args.iter().collect::<Vec<_>>(), callee.hir_id)
            }
            _ => return Ok(()),
        };
        if self.assertion_definition == Some(definition) {
            if arguments.len() != 1 {
                return Err("native assertion has an unrepresented argument inventory".into());
            }
            // The actual reader's Assert statement uses the condition span,
            // not the marker call span (body::marker retains this distinction).
            let condition = arguments[0];
            self.assertions.push(Assertion { span: condition.span, value: json!({
                "intrinsic": key(self.tcx, definition), "call_owner": key(self.tcx, expr.hir_id.owner.def_id.to_def_id()),
                "call_local": expr.hir_id.local_id.as_u32(),
                "condition_owner": key(self.tcx, condition.hir_id.owner.def_id.to_def_id()),
                "condition_local": condition.hir_id.local_id.as_u32(),
                "call_source": self.source.anchor(self.tcx, expr.span, self.budget)?,
                "source": self.source.anchor(self.tcx, condition.span, self.budget)?}) });
        }
        let Some(callee) = self.imported.get(&definition).copied() else {
            return Ok(());
        };
        let native_args = typeck.node_args(generic_node);
        self.budget
            .charge(arguments.len() + native_args.len() + 1, 128, self.depth)?;
        let types = native_args
            .iter()
            .map(|argument| match argument.kind() {
                ty::GenericArgKind::Type(value) => native_type(self.tcx, value, self.budget, 0),
                _ => {
                    Err("native imported call has an unrepresented lifetime/const argument".into())
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let values = arguments.iter().map(|argument| {
            let binding = match &argument.kind {
                hir::ExprKind::Path(path) => match typeck.qpath_res(path, argument.hir_id) {
                    Res::Local(binding) => Some(json!({"owner": key(self.tcx, binding.owner.def_id.to_def_id()),
                        "local": binding.local_id.as_u32()})), _ => None,
                },
                _ => None,
            };
            Ok(json!({"expression_owner": key(self.tcx, argument.hir_id.owner.def_id.to_def_id()),
                "expression_local": argument.hir_id.local_id.as_u32(), "direct_binding": binding,
                "type": native_type(self.tcx, typeck.expr_ty_adjusted(argument), self.budget, 0)?,
                "original_type": native_type(self.tcx, typeck.expr_ty(argument), self.budget, 0)?}))
        }).collect::<Result<Vec<_>, String>>()?;
        let signature = signature(self.tcx, definition, self.budget)?;
        let item_name = self
            .tcx
            .opt_item_name(definition)
            .map(|name| self.budget.text(name.as_str()))
            .transpose()?;
        self.calls.push(Call {
            definition,
            callee,
            span: expr.span,
            type_argument_count: types.len(),
            value_argument_count: values.len(),
            value: json!({"callee": key(self.tcx, definition),
                "item_name_display_only": item_name,
                "call_owner": key(self.tcx, expr.hir_id.owner.def_id.to_def_id()),
                "call_local": expr.hir_id.local_id.as_u32(), "type_arguments": types,
                "value_arguments": values, "declaration_signature": signature,
                "source": self.source.anchor(self.tcx, expr.span, self.budget)?}),
        });
        Ok(())
    }
}

impl<'tcx> Visitor<'tcx> for Walk<'_, 'tcx> {
    type NestedFilter = OnlyBodies;
    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn visit_nested_item(&mut self, _id: hir::ItemId) {
        self.error = Some("native footprint has an unrepresented nested item".into());
    }
    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if self.error.is_some() {
            return;
        }
        if matches!(expr.kind, hir::ExprKind::Closure(_)) {
            self.error = Some("native footprint has an unrepresented closure scope".into());
            return;
        }
        if let Err(reason) = self
            .budget
            .charge(1, 0, self.depth)
            .and_then(|()| self.call(expr))
        {
            self.error = Some(reason);
            return;
        }
        self.depth += 1;
        intravisit::walk_expr(self, expr);
        self.depth -= 1;
    }
}

pub(super) fn calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    imported: &HashMap<DefId, FnId>,
    source: &Source<'_>,
    budget: &mut Budget,
) -> Result<Report, String> {
    let body = tcx
        .hir_maybe_body_owned_by(owner)
        .ok_or("native footprint body is unavailable")?;
    budget.charge(1, 0, 0)?;
    // This is rustc's exact diagnostic identity, not a function spelling.
    // Current builtin artifact ownership remains the existing client frame's
    // obligation; this observation cannot grant or reconstruct that ownership.
    let assertion_definition = tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("verus::verus_builtin::assert_"))
        .filter(|definition| !definition.is_local());
    let mut walk = Walk {
        tcx,
        owner,
        imported,
        source,
        assertion_definition,
        budget,
        calls: Vec::new(),
        assertions: Vec::new(),
        error: None,
        depth: 0,
    };
    walk.visit_body(body);
    if let Some(error) = walk.error {
        return Err(error);
    }
    if tcx.dcx().has_errors().is_some() {
        return Err("native footprint analysis emitted diagnostics".into());
    }
    Ok(Report {
        calls: walk.calls,
        assertions: walk.assertions,
    })
}
