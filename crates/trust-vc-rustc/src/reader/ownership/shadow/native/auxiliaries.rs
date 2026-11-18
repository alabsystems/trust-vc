//! Actual native compiler-owned auxiliary declarations and call relationships.
//!
//! These checks grant no foreign builtin, import or source ownership authority.
//! The publisher supplies allocated roots from the exact private source roles;
//! names and structural lookalikes cannot add roots to that allocation map.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;
use rustc_hir::{
    self as hir,
    def::DefKind,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TypeVisitableExt;

/// Current declaration data for later MIR checking, not ownership permission.
/// Native types remain borrowed in this callback and never leave the worker.
pub(super) struct Definition<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    raw_function_type: ty::Ty<'tcx>,
    function_type: ty::Ty<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
}

pub(super) fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    kind: AuxiliaryKind,
) -> Result<Definition<'tcx>, String> {
    if tcx.dcx().has_errors().is_some()
        || tcx.def_kind(owner) != DefKind::Fn
        || tcx.def_kind(tcx.local_parent(owner)) != DefKind::Mod
        || matches!(tcx.constness(owner), hir::Constness::Const { .. })
        || !tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)).is_empty()
        || tcx.visibility(owner).is_public()
    {
        return Err("an allocated compiler auxiliary has another native declaration scope".into());
    }
    let generics = tcx.generics_of(owner);
    if generics.parent.is_some()
        || generics.parent_count != 0
        || generics.has_self
        || generics.own_params.len() != 2
        || generics
            .own_params
            .iter()
            .enumerate()
            .any(|(index, parameter)| {
                parameter.index as usize != index
                    || parameter.pure_wrt_drop
                    || !matches!(
                        parameter.kind,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false
                        }
                    )
            })
    {
        return Err("an allocated compiler auxiliary changed its actual generic frame".into());
    }
    // Only native Sized-family implicit bounds are expected. In particular,
    // no original predicate, foreign trait or caller-asserted bound is added.
    let clauses = tcx.clauses_of(owner);
    if clauses.parent.is_some() || clauses.clauses.len() > 16 {
        return Err("a compiler auxiliary acquired another clause scope".into());
    }
    let mut sized = [false; 2];
    for (clause, _) in clauses.instantiate_own_identity() {
        let clause = tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id()),
                clause,
            )
            .map_err(|_| "a compiler auxiliary has an unnormalized native predicate")?;
        let Some(ty::ClauseKind::Trait(predicate)) = clause.kind().no_bound_vars() else {
            return Err("a compiler auxiliary has an unsupported predicate kind".into());
        };
        let language = tcx.lang_items();
        if predicate.polarity != ty::ClausePolarity::Positive
            || predicate.trait_ref.args.len() != 1
            || ![
                language.sized_trait(),
                language.meta_sized_trait(),
                language.pointee_sized_trait(),
            ]
            .into_iter()
            .any(|id| id == Some(predicate.def_id()))
        {
            return Err("a compiler auxiliary acquired a foreign or non-Sized native bound".into());
        }
        let ty::Param(parameter) = predicate.self_ty().kind() else {
            return Err("a compiler auxiliary bound has another native generic subject".into());
        };
        let slot = sized
            .get_mut(parameter.index as usize)
            .ok_or("a compiler auxiliary bound refers to a foreign parameter")?;
        if Some(predicate.def_id()) == language.sized_trait() {
            *slot = true;
        }
    }
    if sized != [kind != AuxiliaryKind::MutableTie; 2] {
        return Err("a compiler auxiliary changed its actual Sized relationships".into());
    }
    // Normalize in this actual declaration's native environment. Bound
    // variables remain inside the PolyFnSig and are checked below; no erased
    // free-region equality is accepted as a source-to-shadow region join.
    let native = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id()),
            tcx.fn_sig(owner).instantiate_identity(),
        )
        .map_err(|_| {
            "the compiler auxiliary signature cannot be normalized in its actual owner environment"
        })?;
    let expected_binders = usize::from(kind == AuxiliaryKind::MutableTie);
    if native.bound_vars().len() != expected_binders
        || native
            .bound_vars()
            .iter()
            .any(|bound| !matches!(bound, ty::BoundVariableKind::Region(_)))
    {
        return Err("a compiler auxiliary changed its bound native regions".into());
    }
    let signature = native.skip_binder();
    let unnormalized_function_type = tcx.type_of(owner).instantiate_identity();
    // Only native FnDef owner/binder metadata is observed in the raw value.
    // Keep the original wrapper for the separate mandatory semantic
    // normalization below; this is not an unnormalized semantic type join.
    let raw_function_type = unnormalized_function_type.skip_normalization();
    if !matches!(raw_function_type.kind(), ty::FnDef(definition, _) if definition.as_local() == Some(owner))
    {
        return Err("the allocated auxiliary lost its raw native function-item type".into());
    }
    let function_type = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id()),
            unnormalized_function_type,
        )
        .map_err(|_| {
            "the compiler auxiliary identity type cannot be normalized in its actual declaration"
        })?;
    if !matches!(function_type.kind(), ty::FnDef(definition, _) if definition.as_local() == Some(owner))
    {
        return Err("the allocated auxiliary lost its actual native function-item type".into());
    }
    if !signature.safety().is_safe()
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || signature.splatted().is_some()
    {
        return Err("a compiler auxiliary has an unsupported native calling convention".into());
    }
    let parameter =
        |value: ty::Ty<'_>, index| matches!(value.kind(), ty::Param(p) if p.index == index);
    match kind {
        AuxiliaryKind::ErasedValue | AuxiliaryKind::ShadowValue => {
            if signature.inputs().len() != 1
                || !parameter(signature.inputs()[0], 0)
                || !parameter(signature.output(), 1)
            {
                return Err(
                    "a compiler value producer changed its exact source/target type relationship"
                        .into(),
                );
            }
        }
        AuxiliaryKind::MutableTie => {
            if signature.inputs().len() != 2 {
                return Err("a compiler mutable tie changed its arity".into());
            }
            let ty::Ref(first, first_type, hir::Mutability::Mut) = signature.inputs()[0].kind()
            else {
                return Err("the first compiler tie loan is not mutable".into());
            };
            let ty::Ref(second, second_type, hir::Mutability::Mut) = signature.inputs()[1].kind()
            else {
                return Err("the second compiler tie loan is not mutable".into());
            };
            let ty::Ref(result, result_type, hir::Mutability::Mut) = signature.output().kind()
            else {
                return Err("the compiler tie result is not the retained mutable loan".into());
            };
            if first != second
                || first != result
                || !parameter(*first_type, 0)
                || !parameter(*second_type, 1)
                || *result_type != *first_type
                || !matches!(first.kind(), ty::ReBound(ty::BoundVarIndexKind::Bound(depth), bound)
                    if depth == ty::INNERMOST && bound.var.as_u32() == 0)
            {
                return Err(
                    "a compiler tie laundered its input/result region or referent relationship"
                        .into(),
                );
            }
        }
    }
    let body = tcx.hir_body_owned_by(owner);
    let typeck = tcx.typeck(owner);
    if typeck.tainted_by_errors.is_some()
        || tcx.dcx().has_errors().is_some()
        || body.contract.is_some()
        || body.params.len() != signature.inputs().len()
    {
        return Err("the compiler auxiliary lost its clean current native body/typecheck".into());
    }
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return Err("the compiler auxiliary has another native body shape".into());
    };
    let tail = block
        .expr
        .filter(|_| block.stmts.is_empty())
        .ok_or("the compiler auxiliary has unplanned body statements or no tail")?;
    match kind {
        AuxiliaryKind::ErasedValue | AuxiliaryKind::ShadowValue => {
            if !matches!(tail.kind, hir::ExprKind::Loop(inner, None, hir::LoopSource::Loop, _)
                if inner.stmts.is_empty() && inner.expr.is_none())
            {
                return Err("a compiler value producer has an unplanned native body".into());
            }
        }
        AuxiliaryKind::MutableTie => {
            let hir::PatKind::Binding(_, first, _, None) = body.params[0].pat.kind else {
                return Err("a compiler tie lacks its actual first native input binding".into());
            };
            if !matches!(tail.kind, hir::ExprKind::Path(ref path)
                if typeck.qpath_res(path, tail.hir_id) == Res::Local(first))
            {
                return Err(
                    "a compiler mutable tie does not return only its actual first input".into(),
                );
            }
        }
    }
    Ok(Definition {
        tcx,
        owner,
        raw_function_type,
        function_type,
        signature: native,
    })
}

/// Every actual call to an allocated auxiliary must have the planned source
/// role and exactly that allocated target. No helper name participates.
pub(super) fn check_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    expected: &Expected,
    functions: &BTreeMap<FunctionId, LocalDefId>,
    adts: &BTreeMap<AdtId, LocalDefId>,
    auxiliaries: &BTreeMap<AuxiliaryKind, LocalDefId>,
    declarations: &BTreeMap<AuxiliaryKind, Definition<'tcx>>,
    allocations: &BTreeMap<(Site, Role), allocations::Call>,
    remaining: &mut usize,
) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    let mut calls = std::collections::HashMap::new();
    let mut targets = std::collections::HashMap::new();
    for (kind, owner) in auxiliaries {
        *remaining = remaining
            .checked_sub(1)
            .ok_or("the shared native call allocation budget is exhausted")?;
        if targets.insert(owner.to_def_id(), *kind).is_some() {
            return Err("distinct auxiliaries share one native definition".into());
        }
    }
    for (role, allocation) in allocations {
        *remaining = remaining
            .checked_sub(1)
            .ok_or("the shared native call allocation budget is exhausted")?;
        if *role != allocation.role
            || !expected.emitted.auxiliary_calls.contains_key(role)
            || calls
                .insert(
                    (
                        allocation.owner,
                        allocation.canonical.lo().0,
                        allocation.canonical.hi().0,
                    ),
                    allocation,
                )
                .is_some()
        {
            return Err("parser auxiliary allocations are missing, duplicated or ambiguous".into());
        }
    }
    for function in &expected.program.functions {
        let owner = functions[&function.id];
        let mut visitor = Calls {
            tcx,
            owner,
            typeck: tcx.typeck(owner),
            expected,
            function,
            adts,
            calls: &calls,
            targets: &targets,
            declarations,
            remaining: &mut *remaining,
            seen: &mut seen,
            error: None,
        };
        visitor.visit_body(tcx.hir_body_owned_by(owner));
        if let Some(error) = visitor.error {
            return Err(error);
        }
    }
    // Allocations were checked as an issued-role subset, and duplicate HIR
    // uses refused. Equal cardinality therefore closes the exact inventory.
    if seen.len() != expected.emitted.auxiliary_calls.len() {
        return Err("the native compiler omitted a planned auxiliary call relationship".into());
    }
    Ok(())
}
struct Calls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    expected: &'a Expected,
    function: &'a super::super::program::Function,
    adts: &'a BTreeMap<AdtId, LocalDefId>,
    calls: &'a std::collections::HashMap<(LocalDefId, u32, u32), &'a allocations::Call>,
    targets: &'a std::collections::HashMap<rustc_hir::def_id::DefId, AuxiliaryKind>,
    declarations: &'a BTreeMap<AuxiliaryKind, Definition<'tcx>>,
    remaining: &'a mut usize,
    seen: &'a mut BTreeSet<(super::super::program::Site, Role)>,
    error: Option<String>,
}
impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if self.error.is_some() {
            return;
        }
        if *self.remaining == 0 {
            self.error = Some("the whole auxiliary call inventory exceeds its bound".into());
            return;
        }
        *self.remaining -= 1;
        if expression.hir_id.owner.def_id != self.owner {
            self.error = Some("an auxiliary call walk left its actual native root".into());
            return;
        }
        if let hir::ExprKind::Call(function, arguments) = expression.kind {
            let actual = if let hir::ExprKind::Path(ref path) = function.kind {
                match self.typeck.qpath_res(path, function.hir_id) {
                    Res::Def(DefKind::Fn, target) => self.targets.get(&target).copied(),
                    _ => None,
                }
            } else {
                None
            };
            let file = self
                .tcx
                .sess
                .source_map()
                .lookup_source_file(expression.span.lo());
            let planned = self
                .calls
                .get(&(self.owner, expression.span.lo().0, expression.span.hi().0))
                .copied();
            if let Some(allocation) = planned {
                let role = allocation.role;
                if actual != Some(allocation.kind)
                    || allocation.owner != self.owner
                    || expression.span != allocation.canonical
                    || self.tcx.hir_enclosing_body_owner(expression.hir_id) != self.owner
                    || !matches!(self.tcx.hir_node(expression.hir_id), hir::Node::Expr(current) if std::ptr::eq(current, expression))
                    || !std::ptr::eq(self.typeck, self.tcx.typeck(self.owner))
                    || !self.seen.insert(role)
                    || !matches!(&file.name, FileName::Real(name) if name.local_path() == Some(self.expected.source.as_path()))
                    || !matches!(self.typeck.expr_ty(function).kind(), ty::FnDef(target, _)
                        if target.as_local() == Some(allocation.callee))
                {
                    self.error = Some(format!("a planned auxiliary call changed its actual native allocation/relationship; {}", diagnostics::hir_call(self.tcx, self.owner, self.typeck, expression, self.expected)));
                    return;
                }
                if let Err(error) =
                    self.call_types(expression, function, arguments, allocation.kind, role)
                {
                    self.error = Some(error);
                    return;
                }
            } else if actual.is_some() {
                self.error = Some(format!(
                    "an allocated auxiliary was used outside its complete planned call roles; {}",
                    diagnostics::hir_call(
                        self.tcx,
                        self.owner,
                        self.typeck,
                        expression,
                        self.expected
                    )
                ));
                return;
            }
        }
        intravisit::walk_expr(self, expression);
    }
}

impl<'tcx> Calls<'_, 'tcx> {
    fn call_types(
        &self,
        expression: &'tcx hir::Expr<'tcx>,
        function: &'tcx hir::Expr<'tcx>,
        arguments: &'tcx [hir::Expr<'tcx>],
        kind: AuxiliaryKind,
        role: (Site, Role),
    ) -> Result<(), String> {
        let declaration = self
            .declarations
            .get(&kind)
            .ok_or("the actual call lost its current native declaration data")?;
        let typed = self.typeck.expr_ty(function);
        let ty::FnDef(owner, actual) = typed.kind() else {
            return Err("an auxiliary call is not an actual function-item type".into());
        };
        let ty::FnDef(declared_owner, declared) = declaration.function_type.kind() else {
            return Err(
                "the actual auxiliary declaration has no native function-item binder".into(),
            );
        };
        let ty::FnDef(raw_declared_owner, raw_declared) = declaration.raw_function_type.kind() else {
            return Err("the actual auxiliary declaration has no raw function-item binder".into());
        };
        // Normalization intentionally reconstructs binder metadata from used
        // variables. A FnDef's type arguments may not mention its late-bound
        // signature regions, so that normalized binder is not the metadata
        // against which an unnormalized current expression may be joined.
        // Both declarations above remain actual queries of this allocated
        // owner; only the raw binder supplies this exact native identity join.
        #[cfg(test)]
        let observation = || {
            format!(
                "kind={kind:?} caller={:?} actual_owner={owner:?} declaration_owner={:?} \
                 declaration_type_owner={declared_owner:?} raw_declaration_type_owner={raw_declared_owner:?} \
                 same_tcx={} actual_fn_bound_vars={:?} raw_declaration_fn_bound_vars={:?} \
                 normalized_declaration_fn_bound_vars={:?} declaration_signature_bound_vars={:?} \
                 actual_fn_args={actual:?} actual_node_args={:?} actual_fn_type={typed:?} \
                 normalized_identity_type={:?} normalized_identity_signature={:?} \
                 raw_identity_type={:?} raw_identity_signature={:?} call_hir={:?} function_hir={:?}",
                self.owner,
                declaration.owner,
                std::ptr::eq(*declaration.tcx, *self.tcx),
                actual.bound_vars(),
                raw_declared.bound_vars(),
                declared.bound_vars(),
                declaration.signature.bound_vars(),
                self.typeck.node_args(function.hir_id),
                declaration.function_type,
                declaration.signature,
                declaration.raw_function_type,
                declaration.tcx.fn_sig(declaration.owner).instantiate_identity(),
                expression.hir_id,
                function.hir_id,
            )
        };
        if !std::ptr::eq(*declaration.tcx, *self.tcx)
            || owner.as_local() != Some(declaration.owner)
            || owner != declared_owner
            || owner != raw_declared_owner
            || actual.bound_vars() != raw_declared.bound_vars()
        {
            // Observation-only details stay in the native test callback. In
            // particular, rendered binder/DefId data never supplies a match
            // or substitutes for any of the unchanged checks above.
            #[cfg(test)]
            return Err(format!(
                "an auxiliary call changed its actual declaration/function-item binder; native_binder_observation: {}",
                observation(),
            ));
            #[cfg(not(test))]
            return Err(
                "an auxiliary call changed its actual declaration/function-item binder".into(),
            );
        }
        #[cfg(test)]
        eprintln!("native_binder_join_checked: {}", observation());
        // Function-item binders come from actual late_bound_vars_map, not an
        // assumed PolyFnSig variable count. After that exact declaration join,
        // refuse escaping argument variables before using the binder values.
        // Caller Params and free call-site regions are preserved, not erased.
        let actual = actual.skip_binder();
        let node_args = self.typeck.node_args(function.hir_id);
        if actual.has_escaping_bound_vars()
            || node_args.has_escaping_bound_vars()
            || actual != node_args
            || node_args.len() != 2
        {
            return Err(
                "an auxiliary call has escaping or mismatched native argument variables".into(),
            );
        }
        let first_type = node_args[0]
            .as_type()
            .ok_or("the first actual auxiliary argument is not a native type")?;
        let second_type = node_args[1]
            .as_type()
            .ok_or("the second actual auxiliary argument is not a native type")?;
        // check() validated this identity signature's exact parameter-index
        // mapping. Compare actual native values against that mapping instead
        // of constructing a signature which erases free caller regions.
        let signature = declaration.signature.skip_binder();
        if signature.inputs().len() != arguments.len() {
            return Err("the actual auxiliary call changed its signature arity".into());
        }
        match kind {
            AuxiliaryKind::ErasedValue | AuxiliaryKind::ShadowValue => {
                let planned = self
                    .expected
                    .emitted
                    .auxiliary_calls
                    .get(&role)
                    .filter(|planned| planned.kind == kind)
                    .and_then(|planned| planned.result.as_ref())
                    .ok_or("a compiler value call lost its planned target type")?;
                if arguments.len() != 1
                    || first_type != self.typeck.expr_ty_adjusted(&arguments[0])
                    || second_type != self.typeck.expr_ty(expression)
                {
                    return Err(
                        "a compiler value call changed its actual input/result type arguments"
                            .into(),
                    );
                }
                compare_type(
                    self.tcx,
                    second_type,
                    planned,
                    Frame {
                        generics: &self.function.generics,
                        regions: self.function.regions.len(),
                    },
                    self.adts,
                )
                .map_err(|_| "a compiler value call changed its planned target type")?;
            }
            AuxiliaryKind::MutableTie => {
                if arguments.len() != 2 {
                    return Err(
                        "an actual tie call lost its precise region binder or loan arity".into(),
                    );
                }
                let ty::Ref(first, a, hir::Mutability::Mut) = signature.inputs()[0].kind() else {
                    return Err("the actual first tie input is not its mutable loan".into());
                };
                let ty::Ref(second, b, hir::Mutability::Mut) = signature.inputs()[1].kind() else {
                    return Err("the actual second tie input is not its mutable loan".into());
                };
                let ty::Ref(result, out, hir::Mutability::Mut) = signature.output().kind() else {
                    return Err("the actual tie result is not its first mutable loan".into());
                };
                if first != second
                    || first != result
                    || a != out
                    || !matches!(first.kind(), ty::ReBound(ty::BoundVarIndexKind::Bound(depth), bound)
                        if depth == ty::INNERMOST && bound.var.as_u32() == 0)
                    || !matches!(self.typeck.expr_ty_adjusted(&arguments[0]).kind(), ty::Ref(_, actual, hir::Mutability::Mut) if *actual == first_type)
                    || !matches!(self.typeck.expr_ty_adjusted(&arguments[1]).kind(), ty::Ref(_, actual, hir::Mutability::Mut) if *actual == second_type)
                    || !matches!(self.typeck.expr_ty(expression).kind(), ty::Ref(_, actual, hir::Mutability::Mut) if *actual == first_type)
                {
                    return Err("the actual tie call changed its native region/referent/argument relationship".into());
                }
                // Call-site regions are instantiated by actual native typeck
                // and MIR, not equated to the polymorphic binder by this map.
            }
        }
        Ok(())
    }
}
