//! Original-MIR ownership for legacy primitive values and their Copy products.
//!
//! This does not erase a carrier or complete the general shadow producer.
//! Every source value is a native primitive Copy value or a tuple of them; no reference, ADT,
//! opaque/generic value, destructor or erased storage can cross this lane.
//! The shim must still borrow-check the ORIGINAL root before publication.

use super::*;
use crate::verus_items::VerusItem;
use rustc_middle::{mir, ty};

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}

fn scalar<'tcx>(tcx: ty::TyCtxt<'tcx>, owner: LocalDefId, native: ty::Ty<'tcx>) -> bool {
    let primitive = match native.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) => true,
        ty::Tuple(fields) => fields.is_empty(),
        _ => false,
    };
    primitive && tcx.type_is_copy_modulo_regions(ty::TypingEnv::post_analysis(tcx, owner), native)
}

// Source products and MIR overflow temporaries use the same native type
// recipe. Each component must independently Copy; references, ADTs and type
// parameters never pass because an outer tuple happens to implement Copy.
fn copy_value<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    owner: LocalDefId,
    native: ty::Ty<'tcx>,
    work: &mut usize,
    depth: usize,
) -> Option<()> {
    charge(work, 1)?;
    if depth > 32 {
        return None;
    }
    if scalar(tcx, owner, native) {
        return Some(());
    }
    let ty::Tuple(fields) = native.kind() else {
        return None;
    };
    for field in fields.iter() {
        copy_value(tcx, owner, field, work, depth + 1)?;
    }
    tcx.type_is_copy_modulo_regions(ty::TypingEnv::post_analysis(tcx, owner), native)
        .then_some(())
}

struct Source<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    definition: LocalDefId,
    checked: &'a CheckedModes<'tcx>,
    bindings: HashSet<HirId>,
    observed: HashSet<HirId>,
    locals: HashMap<HirId, CheckedLocal>,
    calls: HashMap<DefId, usize>,
    work: &'a mut usize,
}

impl<'tcx> Source<'_, 'tcx> {
    fn tuple_place(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        depth: usize,
    ) -> Option<Option<(HirId, HirId)>> {
        charge(self.work, 1)?;
        let tcx = self.cx.tcx;
        let typeck = tcx.typeck(self.definition);
        if depth > 128
            || expression.hir_id.owner.def_id != self.definition
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
            || !typeck.expr_adjustments(expression).is_empty()
            || !attrs::verus_attrs(tcx.hir_attrs(expression.hir_id)).is_empty()
        {
            return None;
        }
        copy_value(
            tcx,
            self.definition,
            typeck.expr_ty(expression),
            self.work,
            0,
        )?;
        match expression.kind {
            hir::ExprKind::Path(ref path) => {
                let Res::Local(binding) = typeck.qpath_res(path, expression.hir_id) else {
                    return None;
                };
                self.bindings
                    .contains(&binding)
                    .then_some(Some((binding, expression.hir_id)))
            }
            hir::ExprKind::Field(base, _) => {
                let ty::Tuple(fields) = typeck.expr_ty(base).kind() else {
                    return None;
                };
                let index = typeck.opt_field_index(expression.hir_id)?.as_u32() as usize;
                if fields.get(index).copied()? != typeck.expr_ty(expression) {
                    return None;
                }
                self.tuple_place(base, depth + 1)
            }
            hir::ExprKind::DropTemps(inner) => self.tuple_place(inner, depth + 1),
            _ => {
                // A tuple rvalue has no local-rooted availability access.
                // Its entire value evaluation still needs the ordinary
                // original-expression recipe before projecting a component.
                self.expr(expression, depth + 1)?;
                Some(None)
            }
        }
    }

    fn expr(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        charge(self.work, 1)?;
        let tcx = self.cx.tcx;
        let typeck = tcx.typeck(self.definition);
        if depth > 128
            || expression.hir_id.owner.def_id != self.definition
            || (expression.hir_id != tcx.hir_body_owned_by(self.definition).value.hir_id
                && !self.observed.contains(&expression.hir_id))
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
            || !typeck.expr_adjustments(expression).is_empty()
        {
            return None;
        }
        copy_value(
            tcx,
            self.definition,
            typeck.expr_ty(expression),
            self.work,
            0,
        )?;
        // Proof markers/closures/coercions require the general erasure
        // producer. Ordinary diagnostic notes retain their earlier gates.
        if !attrs::verus_attrs(tcx.hir_attrs(expression.hir_id)).is_empty() {
            return None;
        }
        match expression.kind {
            hir::ExprKind::Lit(_) => Some(()),
            hir::ExprKind::Path(ref path) => {
                let Res::Local(binding) = typeck.qpath_res(path, expression.hir_id) else {
                    return None;
                };
                if !self.bindings.contains(&binding) {
                    return None;
                }
                let usage = self
                    .checked
                    .availability
                    .use_for(expression, super::super::modes::AccessKind::Read)
                    .ok()?;
                (usage.binding == binding
                    && usage.local_use == expression.hir_id
                    && usage.place == expression.hir_id)
                    .then_some(())
            }
            hir::ExprKind::DropTemps(value) => self.expr(value, depth + 1),
            hir::ExprKind::Unary(hir::UnOp::Not | hir::UnOp::Neg, value)
            | hir::ExprKind::Cast(value, _) => self.expr(value, depth + 1),
            hir::ExprKind::Binary(_, left, right) => {
                self.expr(left, depth + 1)?;
                self.expr(right, depth + 1)
            }
            hir::ExprKind::Tup(fields) => {
                for field in fields {
                    self.expr(field, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::Field(_, _) => {
                if let Some((binding, local_use)) = self.tuple_place(expression, depth + 1)? {
                    let usage = self
                        .checked
                        .availability
                        .use_for(expression, super::super::modes::AccessKind::Read)
                        .ok()?;
                    if usage.binding != binding
                        || usage.local_use != local_use
                        || usage.place != expression.hir_id
                    {
                        return None;
                    }
                }
                Some(())
            }
            hir::ExprKind::Assign(place, value, _) => {
                let (binding, local_use) = self.tuple_place(place, depth + 1)??;
                let hir::Node::Pat(pattern) = tcx.hir_node(binding) else {
                    return None;
                };
                // In particular, immutable ghost reassignments cannot use
                // original MIR as an erasure substitute.
                if !matches!(pattern.kind, PatKind::Binding(BindingMode(ByRef::No, mutability), _, _, None) if mutability.is_mut())
                {
                    return None;
                }
                let operation = self.checked.availability.operation_for(expression).ok()?;
                let usage = self
                    .checked
                    .availability
                    .use_for(place, super::super::modes::AccessKind::Assign)
                    .ok()?;
                if operation.kind != super::super::modes::AccessKind::Assign
                    || operation.place != place.hir_id
                    || usage.binding != binding
                    || usage.local_use != local_use
                    || usage.place != place.hir_id
                    || operation.mode != usage.mode
                    || operation.place_mode != usage.place_mode
                {
                    return None;
                }
                self.expr(value, depth + 1)
            }
            hir::ExprKind::Block(block, None) => {
                charge(self.work, self.bindings.len())?;
                let saved = self.bindings.clone();
                for statement in block.stmts {
                    charge(self.work, 1)?;
                    match statement.kind {
                        hir::StmtKind::Let(local) => {
                            let (
                                PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None),
                                Some(init),
                                None,
                            ) = (local.pat.kind, local.init, local.els)
                            else {
                                return None;
                            };
                            let facts = self.checked.local_declarations.get(&local.hir_id)?;
                            if facts.binding != binding
                                || typeck
                                    .pat_adjustments()
                                    .get(local.pat.hir_id)
                                    .is_some_and(|a| !a.is_empty())
                                || typeck
                                    .pat_binding_modes()
                                    .get(binding)
                                    .is_some_and(|b| matches!(b, BindingMode(ByRef::Yes(..), _)))
                                || attrs::verus_attrs(tcx.hir_attrs(local.hir_id))
                                    .iter()
                                    .any(|(a, _)| !matches!(a, VerusAttr::Mode(_)))
                            {
                                return None;
                            }
                            copy_value(
                                tcx,
                                self.definition,
                                typeck.pat_ty(local.pat),
                                self.work,
                                0,
                            )?;
                            self.expr(init, depth + 1)?;
                            self.bindings.insert(binding);
                            self.locals.insert(local.hir_id, *facts);
                        }
                        hir::StmtKind::Semi(value) | hir::StmtKind::Expr(value) => {
                            self.expr(value, depth + 1)?
                        }
                        hir::StmtKind::Item(_) => return None,
                    }
                }
                if let Some(tail) = block.expr {
                    self.expr(tail, depth + 1)?;
                }
                self.bindings = saved;
                Some(())
            }
            hir::ExprKind::If(condition, yes, no) => {
                self.expr(condition, depth + 1)?;
                self.expr(yes, depth + 1)?;
                if let Some(no) = no {
                    self.expr(no, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::Ret(value) => {
                if let Some(value) = value {
                    self.expr(value, depth + 1)?;
                }
                Some(())
            }
            hir::ExprKind::Call(function, arguments) => {
                let hir::ExprKind::Path(ref path) = function.kind else {
                    return None;
                };
                let Res::Def(DefKind::Fn, callee) = typeck.qpath_res(path, function.hir_id) else {
                    return None;
                };
                if !self.cx.fns.contains_key(&callee)
                    && self.cx.verus_item(callee) != Some(VerusItem::Assert)
                {
                    return None;
                }
                // Function-item expressions are not values moved by this
                // lane. The original HIR and MIR independently select this
                // exact callable DefId; ordinary lowering validates its args.
                if !typeck.expr_adjustments(function).is_empty()
                    || !matches!(tcx.hir_node(function.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, function))
                {
                    return None;
                }
                for (position, argument) in arguments.iter().enumerate() {
                    let usage = self
                        .checked
                        .availability
                        .argument_for(expression, position)
                        .ok()?;
                    if usage.argument != argument.hir_id {
                        return None;
                    }
                    self.expr(argument, depth + 1)?;
                }
                *self.calls.entry(callee).or_default() += 1;
                Some(())
            }
            _ => None,
        }
    }
}

/// Completed Modes are necessary but insufficient: the actual source and built
/// MIR must BOTH retain only primitive/product Copy uses, followed by real borrowck.
pub(in crate::reader) fn classify<'tcx>(
    cx: &Cx<'tcx>,
    definition: LocalDefId,
    checked: &CheckedModes<'tcx>,
    work: &mut usize,
) -> Option<NativeOwnership> {
    charge(work, 1)?;
    let tcx = cx.tcx;
    if !cx.legacy_functions.contains(&definition)
        || !checked.legacy_context(cx, definition, definition).ok()?
        || checked.signature.def_id != definition.to_def_id()
        || checked.signature.body_owner != definition
        || tcx.generics_of(definition).count() != 0
        || tcx
            .hir_attrs(tcx.local_def_id_to_hir_id(definition))
            .iter()
            .any(|a| matches!(a, Attribute::Parsed(AttributeKind::CustomMir(..))))
        || !super::super::declaration_modes::original_body_available(tcx, definition)
        || !cx
            .checked_modes
            .borrow()
            .get(&definition)
            .is_some_and(|actual| std::ptr::eq(actual.as_ref(), checked))
    {
        return None;
    }
    checked
        .availability
        .checked(tcx, definition, definition)
        .ok()?;
    checked
        .expressions
        .checked(tcx, definition, definition)
        .ok()?;
    checked.bindings.checked(tcx, definition, definition).ok()?;
    let typeck = tcx.typeck(definition);
    let body = tcx.hir_body_owned_by(definition);
    let signature = typeck.liberated_fn_sigs()[tcx.local_def_id_to_hir_id(definition)];
    copy_value(tcx, definition, signature.output(), work, 0)?;
    let mut observed = HashSet::new();
    for observation in checked.expressions.observations() {
        charge(work, 1)?;
        observed.insert(observation.expression.hir_id);
    }
    let mut source = Source {
        cx,
        definition,
        checked,
        bindings: HashSet::new(),
        observed,
        locals: HashMap::new(),
        calls: HashMap::new(),
        work,
    };
    for (parameter, facts) in body.params.iter().zip(&checked.signature.params) {
        charge(source.work, 1)?;
        let PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) = parameter.pat.kind
        else {
            return None;
        };
        if facts.hir_id != parameter.hir_id || facts.mutable_reference {
            return None;
        }
        copy_value(
            tcx,
            definition,
            typeck.pat_ty(parameter.pat),
            source.work,
            0,
        )?;
        source.bindings.insert(binding);
    }
    if body.params.len() != checked.signature.params.len() {
        return None;
    }
    source.expr(body.value, 0)?;
    let built = tcx.mir_built(definition);
    if built.is_stolen() {
        return None;
    }
    let mir = built.borrow();
    for local in mir.local_decls.iter() {
        copy_value(tcx, definition, local.ty, source.work, 0)?;
    }
    let mut calls = HashMap::new();
    for block in mir.basic_blocks.iter() {
        charge(source.work, block.statements.len().checked_add(1)?)?;
        if let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &block.terminator().kind
        {
            let function = func.ty(&mir.local_decls, tcx);
            let ty::FnDef(callee, _) = function.kind() else {
                return None;
            };
            for argument in args.iter() {
                copy_value(
                    tcx,
                    definition,
                    argument.node.ty(&mir.local_decls, tcx),
                    source.work,
                    0,
                )?;
            }
            copy_value(
                tcx,
                definition,
                destination.ty(&mir.local_decls, tcx).ty,
                source.work,
                0,
            )?;
            *calls.entry(*callee).or_default() += 1;
        }
    }
    if calls != source.calls {
        return None;
    }
    drop(mir); // The real borrow checker may subsequently steal built MIR.
    checked.legacy_context(cx, definition, definition).ok()?;
    checked
        .availability
        .checked(tcx, definition, definition)
        .ok()?;
    Some(NativeOwnership {
        ret: checked.signature.ret,
        locals: source.locals,
    })
}
