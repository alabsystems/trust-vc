//! Identity erasure for original by-value nominal construction and field moves.
//!
//! The body and MIR are borrowed from the SAME original compiler owner. No
//! generated Program, fresh-compiler observation or span equality is accepted
//! as a substitute. This eligibility proof only opens the existing reader
//! transport: the shim must still run original mir_borrowck and independent
//! erase checking before publishing any verification result.

use super::*;
use crate::reader::datatypes;
use crate::reader::modes::{AccessKind, ModeOrigin, VarErasure};
use crate::reader::ownership::{proof_signature, NativeOwnership};
use rustc_hir::def::{CtorKind, Res};
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use std::collections::{HashMap, HashSet};

mod matches;

fn debit(work: &mut usize, amount: usize) -> Option<()> {
    let Some(left) = work.checked_sub(amount) else {
        *work = 0;
        return None;
    };
    *work = left;
    Some(())
}

struct Retained<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    source: SourceInventory<'tcx>,
    work: &'a mut usize,
    types: HashSet<ty::Ty<'tcx>>,
    bindings: HashSet<HirId>,
    declared: HashSet<HirId>,
    locals: HashMap<HirId, crate::reader::modes::CheckedLocal>,
    uses: HashSet<HirId>,
    arguments: HashSet<(HirId, usize)>,
    calls: HashMap<(DefId, ty::GenericArgs<'tcx>), usize>,
    nominal_operation: bool,
    matches: HashSet<HirId>,
}

impl<'tcx> Retained<'_, 'tcx> {
    fn charge(&mut self, amount: usize) -> Option<()> {
        debit(self.work, amount)
    }

    // Every field is retained, including unused fields. A kept outer nominal
    // type is insufficient when one of its actual declarations erases storage.
    fn native_type(&mut self, native: ty::Ty<'tcx>, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth > 64 {
            return None;
        }
        if !self.types.insert(native) {
            return Some(());
        }
        let tcx = self.source.tcx;
        match native.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Param(_) => Some(()),
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.native_type(field, depth + 1)?;
                }
                Some(())
            }
            ty::Adt(adt, arguments) => {
                let local = adt.did().as_local()?;
                if !(adt.is_struct() || adt.is_enum()) || self.cx.adt_id(adt.did()).is_none() {
                    return None;
                }
                let item = attrs::item_attrs_with_work(
                    tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
                    self.work,
                )
                .ok()?;
                if item.external
                    || item.external_body
                    || item.mode.is_some()
                    || !item.unsupported.is_empty()
                {
                    return None;
                }
                for argument in arguments.iter() {
                    self.charge(1)?;
                    self.native_type(argument.as_type()?, depth + 1)?;
                }
                for variant in adt.variants().iter() {
                    self.charge(1)?;
                    if adt.is_enum() {
                        let owner = variant.def_id.as_local()?;
                        if attrs::verus_attrs_with_work(
                            tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
                            self.work,
                        )
                        .ok()?
                        .iter()
                        .any(|(attribute, _)| *attribute != attrs::VerusAttr::VerusMacro)
                        {
                            return None;
                        }
                    }
                    for field in &variant.fields {
                        self.charge(1)?;
                        if datatypes::field_mode_with_work(
                            tcx,
                            field,
                            tcx.def_span(field.did),
                            self.work,
                        )
                        .ok()?
                            != Mode::Exec
                        {
                            return None;
                        }
                        self.native_type(
                            tcx.type_of(field.did)
                                .instantiate(tcx, arguments)
                                .skip_normalization(),
                            depth + 1,
                        )?;
                    }
                }
                Some(())
            }
            // References, aliases, foreign carriers and erased/uninhabited
            // proxies require the nonidentity producer, not this proof.
            _ => None,
        }
    }

    fn allocated(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        self.charge(1)?;
        let source = &self.source;
        if depth > 128
            || expression.hir_id.owner.def_id != source.definition
            || !matches!(source.tcx.hir_node(expression.hir_id), hir::Node::Expr(current) if std::ptr::eq(current, expression))
            || !source.typeck.expr_adjustments(expression).is_empty()
            || !attrs::verus_attrs_with_work(source.tcx.hir_attrs(expression.hir_id), self.work)
                .ok()?
                .is_empty()
        {
            return None;
        }
        Some(())
    }

    fn plain(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        self.allocated(expression, depth)?;
        self.native_type(self.source.typeck.expr_ty(expression), 0)
    }

    fn observed(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        self.plain(expression, depth)?;
        let source = &self.source;
        let rows = source
            .checked
            .expressions
            .for_expression(source.tcx, source.definition, source.definition, expression)
            .ok()?;
        debit(self.work, rows.len())?;
        if rows.iter().any(|row| {
            row.result == Mode::Spec
                || row.context.pure
                || row.context.proof_in_spec
                || row.context.assert_by
                || row.native_type != row.adjusted_type
        }) {
            return None;
        }
        Some(())
    }

    // Prefix nodes are places, not independent value reads. The final access
    // carries the real mode walk's complete local-rooted availability row.
    fn place(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<(HirId, HirId)> {
        self.plain(expression, depth)?;
        match expression.kind {
            hir::ExprKind::Path(ref path) => {
                let Res::Local(binding) = self.source.typeck.qpath_res(path, expression.hir_id)
                else {
                    return None;
                };
                self.bindings
                    .contains(&binding)
                    .then_some((binding, expression.hir_id))
            }
            hir::ExprKind::Field(base, _) => {
                let index = self.source.typeck.opt_field_index(expression.hir_id)?;
                let ty::Adt(adt, arguments) = self.source.typeck.expr_ty(base).kind() else {
                    return None;
                };
                if !adt.is_struct() {
                    return None;
                }
                let field = adt.non_enum_variant().fields.get(index)?;
                if self
                    .source
                    .tcx
                    .type_of(field.did)
                    .instantiate(self.source.tcx, arguments)
                    .skip_normalization()
                    != self.source.typeck.expr_ty(expression)
                {
                    return None;
                }
                self.nominal_operation = true;
                self.place(base, depth + 1)
            }
            _ => None,
        }
    }

    fn argument(
        &mut self,
        call: &'tcx hir::Expr<'tcx>,
        value: &'tcx hir::Expr<'tcx>,
        position: usize,
        mode: Mode,
        depth: usize,
    ) -> Option<()> {
        self.charge(1)?;
        let row = self
            .source
            .checked
            .availability
            .argument_for(call, position)
            .ok()?;
        if row.argument != value.hir_id
            || row.mode != mode
            || row.erased
            || mode == Mode::Spec
            || !self.arguments.insert((call.hir_id, position))
        {
            return None;
        }
        self.value(value, depth + 1)
    }

    fn value(&mut self, expression: &'tcx hir::Expr<'tcx>, depth: usize) -> Option<()> {
        self.observed(expression, depth)?;
        match expression.kind {
            hir::ExprKind::Block(block, None) => self.block(block, depth + 1),
            hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Normal) => {
                self.ordinary_match(expression, scrutinee, arms, depth + 1)
            }
            hir::ExprKind::Tup(fields) if fields.is_empty() => Some(()),
            hir::ExprKind::Path(ref path)
                if matches!(
                    self.source.typeck.qpath_res(path, expression.hir_id),
                    Res::Def(DefKind::Ctor(_, CtorKind::Const), _)
                ) =>
            {
                let ty::Adt(adt, _) = self.source.typeck.expr_ty(expression).kind() else {
                    return None;
                };
                let (_, variant) = datatypes::constructor_variant(
                    *adt,
                    self.source.typeck.qpath_res(path, expression.hir_id),
                )?;
                if !variant.fields.is_empty() {
                    return None;
                }
                self.nominal_operation = true;
                Some(())
            }
            hir::ExprKind::Path(_) | hir::ExprKind::Field(..) => {
                let (binding, local_use) = self.place(expression, depth + 1)?;
                let row = self
                    .source
                    .checked
                    .availability
                    .use_for(expression, AccessKind::Read)
                    .ok()?;
                if row.binding != binding
                    || row.local_use != local_use
                    || row.place != expression.hir_id
                    || row.binding_mode != Mode::Proof
                    || row.place_mode != Mode::Proof
                    || row.mode != Mode::Proof
                    || row.erasure != VarErasure::Keep
                    || !self.uses.insert(expression.hir_id)
                {
                    return None;
                }
                Some(())
            }
            hir::ExprKind::Struct(ref path, fields, hir::StructTailExpr::None) => {
                let ty::Adt(adt, arguments) = self.source.typeck.expr_ty(expression).kind() else {
                    return None;
                };
                if !adt.is_struct()
                    || !matches!(self.source.typeck.qpath_res(path, expression.hir_id), Res::Def(DefKind::Struct, actual) if actual == adt.did())
                    || fields.len() != adt.non_enum_variant().fields.len()
                {
                    return None;
                }
                let mut written = HashSet::new();
                for (position, field) in fields.iter().enumerate() {
                    self.charge(1)?;
                    let index = self.source.typeck.opt_field_index(field.hir_id)?;
                    let actual = adt.non_enum_variant().fields.get(index)?;
                    if !written.insert(index)
                        || self
                            .source
                            .tcx
                            .type_of(actual.did)
                            .instantiate(self.source.tcx, arguments)
                            .skip_normalization()
                            != self.source.typeck.expr_ty(field.expr)
                    {
                        return None;
                    }
                    // Positions are written evaluation order; native field
                    // indices independently identify their declaration slots.
                    self.argument(expression, field.expr, position, Mode::Exec, depth + 1)?;
                }
                self.nominal_operation = true;
                Some(())
            }
            hir::ExprKind::Call(function, values) => {
                self.allocated(function, depth + 1)?;
                let hir::ExprKind::Path(ref path) = function.kind else {
                    return None;
                };
                let resolution = self.source.typeck.qpath_res(path, function.hir_id);
                let ty::FnDef(target, arguments) = self.source.typeck.expr_ty(function).kind()
                else {
                    return None;
                };
                if !arguments.bound_vars().is_empty() {
                    return None;
                }
                let arguments = arguments.no_bound_vars()?;
                match resolution {
                    Res::Def(DefKind::Fn, actual) if actual == *target => {
                        let signature = proof_signature(self.cx, *target)?;
                        if signature.params.len() != values.len() {
                            return None;
                        }
                        for (position, value) in values.iter().enumerate() {
                            self.argument(expression, value, position, Mode::Proof, depth + 1)?;
                        }
                        let count = self.calls.entry((*target, arguments)).or_default();
                        *count = count.checked_add(1)?;
                        Some(())
                    }
                    Res::Def(DefKind::Ctor(_, CtorKind::Fn), actual) if actual == *target => {
                        let ty::Adt(adt, adt_arguments) =
                            self.source.typeck.expr_ty(expression).kind()
                        else {
                            return None;
                        };
                        let (_, variant) = datatypes::constructor_variant(*adt, resolution)?;
                        if !(adt.is_struct() || adt.is_enum())
                            || variant.fields.len() != values.len()
                            || arguments != *adt_arguments
                        {
                            return None;
                        }
                        for (position, (field, value)) in
                            variant.fields.iter().zip(values).enumerate()
                        {
                            self.charge(1)?;
                            if self
                                .source
                                .tcx
                                .type_of(field.did)
                                .instantiate(self.source.tcx, adt_arguments)
                                .skip_normalization()
                                != self.source.typeck.expr_ty(value)
                            {
                                return None;
                            }
                            self.argument(expression, value, position, Mode::Exec, depth + 1)?;
                        }
                        self.nominal_operation = true;
                        Some(())
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn block(&mut self, block: &'tcx hir::Block<'tcx>, depth: usize) -> Option<()> {
        self.charge(self.bindings.len())?;
        let outer = self.bindings.clone();
        for statement in block.stmts {
            self.charge(1)?;
            match statement.kind {
                hir::StmtKind::Let(local) => {
                    let (
                        hir::PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None),
                        Some(init),
                        None,
                    ) = (local.pat.kind, local.init, local.els)
                    else {
                        return None;
                    };
                    let fact = *self.source.checked.local_declarations.get(&local.hir_id)?;
                    if fact.binding != binding
                        || fact.declared.mode != Mode::Proof
                        || fact.effective != Mode::Proof
                        || !matches!(fact.declared.origin, ModeOrigin::Attribute(_))
                        || self
                            .source
                            .typeck
                            .pat_adjustments()
                            .get(local.pat.hir_id)
                            .is_some_and(|row| !row.is_empty())
                        || self
                            .source
                            .typeck
                            .pat_binding_modes()
                            .get(binding)
                            .is_some_and(|mode| matches!(mode, BindingMode(ByRef::Yes(..), _)))
                        || attrs::verus_attrs_with_work(
                            self.source.tcx.hir_attrs(local.hir_id),
                            self.work,
                        )
                        .ok()?
                        .iter()
                        .any(|(attribute, _)| {
                            !matches!(
                                attribute,
                                attrs::VerusAttr::Mode(_) | attrs::VerusAttr::LetMarker(_)
                            )
                        })
                    {
                        return None;
                    }
                    self.native_type(self.source.typeck.pat_ty(local.pat), 0)?;
                    self.value(init, depth + 1)?;
                    self.bindings.insert(binding);
                    self.declared.insert(binding);
                    self.locals.insert(local.hir_id, fact);
                }
                hir::StmtKind::Semi(value) | hir::StmtKind::Expr(value) => {
                    self.value(value, depth + 1)?
                }
                _ => return None,
            }
        }
        if let Some(tail) = block.expr {
            self.value(tail, depth + 1)?;
        }
        self.bindings = outer;
        Some(())
    }

    fn body(&mut self) -> Option<()> {
        let source = &self.source;
        let body = source.body;
        if source.signature.function_mode != Mode::Proof
            || source.signature.result.mode != Mode::Proof
        {
            return None;
        }
        self.native_type(self.source.signature.result.original, 0)?;
        for (parameter, mode) in body
            .params
            .iter()
            .zip(&self.source.checked.signature.params)
        {
            debit(self.work, 1)?;
            let hir::PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) =
                parameter.pat.kind
            else {
                return None;
            };
            if parameter.hir_id != mode.hir_id
                || mode.declared.mode != Mode::Proof
                || mode.mutable_reference
            {
                return None;
            }
            self.bindings.insert(binding);
            self.declared.insert(binding);
        }
        for parameter in body.params {
            self.native_type(self.source.typeck.pat_ty(parameter.pat), 0)?;
        }
        self.value(body.value, 0)?;
        if !self.nominal_operation
            || self.uses.len() != self.source.uses.len()
            || self.arguments.len() != self.source.arguments.len()
            || !self.source.operations.is_empty()
            || self.declared.len() != self.source.bindings.len()
            || self.matches.len() != self.source.controls.len()
        {
            return None;
        }
        for (pattern, slot) in &self.source.bindings {
            debit(self.work, 1)?;
            if slot.mode != Mode::Proof || !self.declared.contains(&pattern.hir_id) {
                return None;
            }
        }
        for control in &self.source.controls {
            debit(self.work, 1)?;
            if !matches!(control, Control::Match { expression, .. } if self.matches.contains(&expression.hir_id))
            {
                return None;
            }
        }
        for row in &self.source.adjustments {
            debit(self.work, 1)?;
            if !row.kinds.is_empty() || row.reborrow.is_some() {
                return None;
            }
        }
        Some(())
    }
}

pub(in crate::reader::ownership) fn classify<'tcx>(
    cx: &Cx<'tcx>,
    definition: LocalDefId,
    work: &mut usize,
) -> Option<NativeOwnership> {
    // Canonical Rc identity, complete modes/bindings/availability, actual
    // original body pointer and native ABI are validated by this inventory.
    debit(work, 1)?;
    proof_signature(cx, definition.to_def_id())?;
    let source = SourceInventory::collect_with_work(cx, definition, work).ok()?;
    let mut retained = Retained {
        cx,
        source,
        work,
        types: HashSet::new(),
        bindings: HashSet::new(),
        declared: HashSet::new(),
        locals: HashMap::new(),
        uses: HashSet::new(),
        arguments: HashSet::new(),
        calls: HashMap::new(),
        nominal_operation: false,
        matches: HashSet::new(),
    };
    retained.body()?;
    let tcx = cx.tcx;
    // This is the compiler's original built body for that exact owner, not
    // reconstructed MIR. No type, predicate, Drop or Copy frame is replaced.
    let built = tcx.mir_built(definition);
    if built.is_stolen() {
        return None;
    }
    let mir = built.borrow();
    if mir.arg_count != retained.source.body.params.len()
        || mir.return_ty() != retained.source.signature.result.original
    {
        return None;
    }
    for local in mir.local_decls.iter() {
        retained.native_type(local.ty, 0)?;
    }
    let mut calls = HashMap::new();
    for block in mir.basic_blocks.iter() {
        retained.charge(block.statements.len().checked_add(1)?)?;
        if let mir::TerminatorKind::Call { func, .. } = &block.terminator().kind {
            let ty::FnDef(target, arguments) = *func.ty(&mir.local_decls, tcx).kind() else {
                return None;
            };
            if !arguments.bound_vars().is_empty() {
                return None;
            }
            let arguments = arguments.no_bound_vars()?;
            let count = calls.entry((target, arguments)).or_insert(0usize);
            *count = count.checked_add(1)?;
        }
    }
    if calls != retained.calls {
        return None;
    }
    drop(mir); // Canonical borrowck must be free to steal this original MIR.
    retained
        .source
        .revalidate_with_work(cx, retained.work)
        .ok()?;
    Some(NativeOwnership {
        ret: retained.source.checked.signature.ret,
        locals: retained.locals,
    })
}
