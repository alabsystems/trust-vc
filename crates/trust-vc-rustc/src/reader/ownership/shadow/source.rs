//! Current native source data for the production shadow translator.
//!
//! This is an unmaterialized inventory, not an executed ownership check.
//! Nonidentity type/signature requirements remain explicit until a real
//! native shadow declaration/graph has been produced and joined back to it.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

extern crate rustc_abi;

use rustc_ast::{BindingMode, ByRef};
use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir, HirId};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use std::rc::Rc;
use trust_vc_vcir::Mode;

use super::super::super::modes::{AdjustmentUse, ArgumentUse, CheckedModes, Operation, PlaceUse};
use super::super::super::{attrs, declaration_modes, Cx};

pub(in crate::reader::ownership::shadow) mod graph;
pub(in crate::reader::ownership) mod retained;

/// A request to the native producer, never a fabricated rustc type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TypeRequirement {
    /// A retained value must keep its original native type and ownership.
    Retained,
    /// The target must be inhabited and inert for ownership. Position-aware
    /// erasure may use native unit rather than preserve the original scalar.
    /// The producer must preserve normal continuation and evaluation.
    InhabitedNativeProxy,
    /// A real shadow declaration/signature is needed. In particular `!`
    /// must not survive as a Spec proxy and delete tracked-use checks.
    ShadowDeclaration,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct TypeSlot<'tcx> {
    pub(super) original: ty::Ty<'tcx>,
    pub(super) mode: Mode,
    pub(super) requirement: TypeRequirement,
}

impl<'tcx> TypeSlot<'tcx> {
    fn request(original: ty::Ty<'tcx>, mode: Mode) -> Self {
        let requirement = if mode != Mode::Spec {
            TypeRequirement::Retained
        } else if original.is_unit()
            || matches!(original.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
        {
            TypeRequirement::InhabitedNativeProxy
        } else {
            TypeRequirement::ShadowDeclaration
        };
        Self {
            original,
            mode,
            requirement,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Signature<'tcx> {
    pub(super) function_mode: Mode,
    pub(super) parameters: Vec<(HirId, TypeSlot<'tcx>)>,
    pub(super) result: TypeSlot<'tcx>,
    /// Syntactic observations only: Ty::walk visits type arguments, not ADT
    /// field definitions. These are not a complete mutable-interface census.
    pub(super) observed_mutable_interfaces: Vec<InterfacePosition>,
    /// These slots still need a bounded, normalized native type/field closure.
    /// No observation here can remove the existing parameter/return gates.
    pub(super) unexpanded_interfaces: Vec<InterfacePosition>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum InterfacePosition {
    Parameter(HirId),
    Return,
}

fn spend(remaining: &mut usize, amount: usize) -> Result<(), String> {
    *remaining = remaining
        .checked_sub(amount)
        .ok_or("shadow source work exceeds the caller's shared bound")?;
    Ok(())
}

fn interface_requirements(
    native: ty::Ty<'_>,
    remaining: &mut usize,
) -> Result<(bool, bool), String> {
    let mut mutable = false;
    let mut unexpanded = false;
    // These are syntactic observations, not a native ADT-field closure.
    // Traverse once and debit before inspecting each actual type argument.
    spend(remaining, 1)?;
    let mut arguments = native.walk();
    loop {
        spend(remaining, 1)?;
        let Some(argument) = arguments.next() else {
            break;
        };
        if let Some(value) = argument.as_type() {
            mutable |= matches!(value.kind(), ty::Ref(_, _, mutability) if mutability.is_mut());
            unexpanded |= matches!(
                value.kind(),
                ty::Adt(..) | ty::Param(..) | ty::Alias(..) | ty::Dynamic(..)
            );
        }
        if mutable && unexpanded {
            break;
        }
    }
    Ok((mutable, unexpanded))
}

#[derive(Clone, Debug)]
pub(super) enum Control<'tcx> {
    Match {
        expression: &'tcx hir::Expr<'tcx>,
        scrutinee: &'tcx hir::Expr<'tcx>,
        arms: &'tcx [hir::Arm<'tcx>],
        scrutinee_mode: Mode,
        result_mode: Mode,
    },
    If {
        expression: &'tcx hir::Expr<'tcx>,
        condition: &'tcx hir::Expr<'tcx>,
        then_value: &'tcx hir::Expr<'tcx>,
        else_value: Option<&'tcx hir::Expr<'tcx>>,
    },
    Return {
        expression: &'tcx hir::Expr<'tcx>,
        value: Option<&'tcx hir::Expr<'tcx>>,
        required_mode: Mode,
    },
}

/// Actual direct-call edges. A native FnDef is data about this source call,
/// not an instantiated trait-resolution or foreign-body permission.
pub(super) struct Call<'tcx> {
    pub(super) expression: &'tcx hir::Expr<'tcx>,
    pub(super) callee: &'tcx hir::Expr<'tcx>,
    pub(super) target: rustc_hir::def_id::DefId,
    pub(super) arguments: ty::GenericArgs<'tcx>,
    pub(super) values: &'tcx [hir::Expr<'tcx>],
}

pub(super) struct SourceInventory<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    checked: Rc<CheckedModes<'tcx>>,
    pub(super) signature: Signature<'tcx>,
    pub(super) bindings: Vec<(&'tcx hir::Pat<'tcx>, TypeSlot<'tcx>)>,
    pub(super) controls: Vec<Control<'tcx>>,
    pub(super) calls: Vec<Call<'tcx>>,
    pub(super) uses: Vec<PlaceUse>,
    pub(super) arguments: Vec<ArgumentUse>,
    pub(super) adjustments: Vec<AdjustmentUse>,
    pub(super) operations: Vec<Operation>,
}

impl<'tcx> SourceInventory<'tcx> {
    pub(super) fn collect(cx: &Cx<'tcx>, definition: LocalDefId) -> Result<Self, String> {
        Self::collect_with_work(cx, definition, &mut 262_144)
    }

    pub(super) fn collect_with_work(
        cx: &Cx<'tcx>,
        definition: LocalDefId,
        remaining: &mut usize,
    ) -> Result<Self, String> {
        *remaining = remaining
            .checked_sub(1)
            .ok_or("the complete source graph exceeds its shared work bound")?;
        let tcx = cx.tcx;
        if tcx.def_kind(definition) != DefKind::Fn
            || tcx.def_kind(tcx.local_parent(definition)) != DefKind::Mod
            || tcx.is_typeck_child(definition.to_def_id())
            || !declaration_modes::original_body_available(tcx, definition)
            || tcx.dcx().has_errors().is_some()
        {
            return Err("a shadow source needs a current original free-function root".into());
        }
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(definition));
        let item = attrs::item_attrs_with_work(attributes, remaining)?;
        if item.external || item.external_body || item.uninterp || !item.unsupported.is_empty() || {
            // Preserve the old short circuit: external/unsupported items
            // never inspect this remaining native attribute payload.
            let mut custom_mir = false;
            for attribute in attributes {
                spend(remaining, 1)?;
                if matches!(attribute, Attribute::Parsed(AttributeKind::CustomMir(..))) {
                    custom_mir = true;
                    break;
                }
            }
            custom_mir
        } {
            return Err(
                "external, unsupported or injected native bodies cannot prepare a shadow".into(),
            );
        }
        let checked = cx
            .checked_modes
            .borrow()
            .get(&definition)
            .cloned()
            .ok_or("a shadow source requires the current complete mode walk")?;
        if checked.signature.def_id != definition.to_def_id()
            || checked.signature.body_owner != definition
        {
            return Err("shadow signature modes belong to another native source root".into());
        }
        let body = tcx.hir_body_owned_by(definition);
        let typeck = tcx.typeck(definition);
        if typeck.tainted_by_errors.is_some() || body.contract.is_some() {
            return Err(
                "tainted or native-contract bodies need a distinct complete translation".into(),
            );
        }
        checked.legacy_context_with_work(cx, definition, definition, remaining)?;
        checked
            .availability
            .checked_with_work(tcx, definition, definition, remaining)?;
        checked
            .bindings
            .checked_with_work(tcx, definition, definition, remaining)?;
        checked
            .expressions
            .checked_with_work(tcx, definition, definition, remaining)?;
        let native_signature = typeck.liberated_fn_sigs()[tcx.local_def_id_to_hir_id(definition)];
        if native_signature.safety().is_unsafe()
            || native_signature.abi() != rustc_abi::ExternAbi::Rust
            || native_signature.c_variadic()
            || body.params.len() != checked.signature.params.len()
        {
            return Err("the actual native signature is outside the shadow source contract".into());
        }
        let mut parameters = Vec::new();
        for (parameter, modes) in body.params.iter().zip(&checked.signature.params) {
            spend(remaining, 1)?;
            if parameter.hir_id != modes.hir_id
                || !matches!(
                    parameter.pat.kind,
                    hir::PatKind::Binding(BindingMode(ByRef::No, _), _, _, None)
                )
            {
                return Err(
                    "shadow formals require their exact current plain native bindings".into(),
                );
            }
            parameters.push((
                parameter.hir_id,
                TypeSlot::request(typeck.pat_ty(parameter.pat), modes.declared.mode),
            ));
        }
        let mut mutable_interfaces = Vec::new();
        let mut unexpanded_interfaces = Vec::new();
        for (hir_id, slot) in &parameters {
            let (mutable, unexpanded) = interface_requirements(slot.original, remaining)?;
            if mutable {
                mutable_interfaces.push(InterfacePosition::Parameter(*hir_id));
            }
            if unexpanded {
                unexpanded_interfaces.push(InterfacePosition::Parameter(*hir_id));
            }
        }
        let (mutable, unexpanded) = interface_requirements(native_signature.output(), remaining)?;
        if mutable {
            mutable_interfaces.push(InterfacePosition::Return);
        }
        if unexpanded {
            unexpanded_interfaces.push(InterfacePosition::Return);
        }
        let signature = Signature {
            function_mode: checked.signature.mode,
            parameters,
            result: TypeSlot::request(native_signature.output(), checked.signature.ret.mode),
            observed_mutable_interfaces: mutable_interfaces,
            unexpanded_interfaces,
        };
        let mut bindings = Vec::new();
        for (pattern, mode) in checked.bindings.observations() {
            spend(remaining, 1)?;
            bindings.push((pattern, TypeSlot::request(typeck.pat_ty(pattern), mode)));
        }
        let inventory_cost = checked
            .availability
            .uses()
            .len()
            .checked_add(checked.availability.arguments().len())
            .and_then(|n| n.checked_add(checked.availability.operations().len()))
            .and_then(|n| n.checked_add(checked.availability.adjustments().len()))
            .ok_or("source inventory size overflow")?;
        *remaining = remaining
            .checked_sub(inventory_cost)
            .ok_or("source inventory exceeds the shared graph work bound")?;
        for adjustment in checked.availability.adjustments() {
            spend(remaining, 1)?;
            // to_vec clones this nested vector as well as its outer row.
            spend(remaining, adjustment.kinds.len())?;
        }
        let mut collector = Controls {
            tcx,
            definition,
            typeck,
            checked: &checked,
            values: Vec::new(),
            calls: Vec::new(),
            problem: None,
            depth: 0,
            remaining,
        };
        collector.visit_body(body);
        if let Some(problem) = collector.problem {
            return Err(problem);
        }
        let controls = collector.values;
        let calls = collector.calls;
        let inventory = Self {
            tcx,
            definition,
            body,
            typeck,
            uses: checked.availability.uses().to_vec(),
            arguments: checked.availability.arguments().to_vec(),
            adjustments: checked.availability.adjustments().to_vec(),
            operations: checked.availability.operations().to_vec(),
            checked,
            signature,
            bindings,
            controls,
            calls,
        };
        inventory.revalidate_with_work(cx, remaining)?;
        Ok(inventory)
    }

    fn current(&self, cx: &Cx<'tcx>, remaining: Option<&mut usize>) -> Result<(), String> {
        let tcx = cx.tcx;
        if !std::ptr::eq(*tcx, *self.tcx)
            || !declaration_modes::original_body_available(tcx, self.definition)
            || !std::ptr::eq(tcx.hir_body_owned_by(self.definition), self.body)
            || !std::ptr::eq(tcx.typeck(self.definition), self.typeck)
            || !cx
                .checked_modes
                .borrow()
                .get(&self.definition)
                .is_some_and(|actual| Rc::ptr_eq(actual, &self.checked))
        {
            return Err(
                "the shadow inventory changed its original native source or complete mode Rc"
                    .into(),
            );
        }
        match remaining {
            Some(work) => {
                self.checked
                    .legacy_context_with_work(cx, self.definition, self.definition, work)?
            }
            None => self
                .checked
                .legacy_context(cx, self.definition, self.definition)?,
        };
        Ok(())
    }

    pub(super) fn revalidate(&self, cx: &Cx<'tcx>) -> Result<(), String> {
        self.current(cx, None)?;
        let tcx = cx.tcx;
        self.checked
            .availability
            .checked(tcx, self.definition, self.definition)?;
        self.checked
            .bindings
            .checked(tcx, self.definition, self.definition)?;
        self.checked
            .expressions
            .checked(tcx, self.definition, self.definition)?;
        Ok(())
    }

    pub(super) fn revalidate_with_work(
        &self,
        cx: &Cx<'tcx>,
        remaining: &mut usize,
    ) -> Result<(), String> {
        spend(remaining, 1)?;
        self.current(cx, Some(remaining))?;
        let tcx = cx.tcx;
        self.checked.availability.checked_with_work(
            tcx,
            self.definition,
            self.definition,
            remaining,
        )?;
        self.checked.bindings.checked_with_work(
            tcx,
            self.definition,
            self.definition,
            remaining,
        )?;
        self.checked.expressions.checked_with_work(
            tcx,
            self.definition,
            self.definition,
            remaining,
        )?;
        Ok(())
    }
}

struct Controls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>,
    checked: &'a CheckedModes<'tcx>,
    values: Vec<Control<'tcx>>,
    calls: Vec<Call<'tcx>>,
    problem: Option<String>,
    depth: usize,
    remaining: &'a mut usize,
}

impl<'tcx> Visitor<'tcx> for Controls<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if self.problem.is_some() {
            return;
        }
        if *self.remaining == 0 || self.depth >= 128 {
            self.problem = Some("shadow control-flow inventory exceeds its bound".into());
            return;
        }
        *self.remaining -= 1;
        match expression.kind {
            hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Normal) => {
                match self.checked.matches.for_match(
                    self.tcx,
                    self.definition,
                    self.definition,
                    self.typeck,
                    expression,
                    scrutinee,
                    arms,
                ) {
                    Ok(facts) => self.values.push(Control::Match {
                        expression,
                        scrutinee,
                        arms,
                        scrutinee_mode: facts.scrutinee_mode,
                        result_mode: facts.result_mode,
                    }),
                    Err(detail) => {
                        self.problem = Some(detail);
                        return;
                    }
                }
            }
            hir::ExprKind::If(condition, then_value, else_value) => {
                self.values.push(Control::If {
                    expression,
                    condition,
                    then_value,
                    else_value,
                });
            }
            hir::ExprKind::Ret(value) => {
                self.values.push(Control::Return {
                    expression,
                    value,
                    required_mode: self.checked.signature.ret.mode,
                });
            }
            hir::ExprKind::Call(callee, values) => {
                let ty::FnDef(target, arguments) = self.typeck.expr_ty(callee).kind() else {
                    self.problem =
                        Some("a source call has no actual direct native FnDef target".into());
                    return;
                };
                if !matches!(self.tcx.hir_node(callee.hir_id), hir::Node::Expr(current) if std::ptr::eq(current, callee))
                {
                    self.problem = Some("a source callee changed native HIR allocation".into());
                    return;
                }
                if !arguments.bound_vars().is_empty() {
                    self.problem = Some(
                        "a native call has bound arguments requiring their complete source frame"
                            .into(),
                    );
                    return;
                }
                let Some(arguments) = arguments.no_bound_vars() else {
                    self.problem = Some("a native call has escaping bound arguments".into());
                    return;
                };
                self.calls.push(Call {
                    expression,
                    callee,
                    target: *target,
                    arguments,
                    values,
                });
            }
            hir::ExprKind::MethodCall(..) => {
                self.problem = Some("a method/trait call needs its exact current Instance/signature/receiver mapping before shadow closure".into());
                return;
            }
            hir::ExprKind::Closure(_) | hir::ExprKind::Loop(..) | hir::ExprKind::Match(..) => {
                self.problem = Some("this native closure/loop/desugared control flow needs its own complete shadow mapping".into());
                return;
            }
            _ => {}
        }
        self.depth += 1;
        intravisit::walk_expr(self, expression);
        self.depth -= 1;
    }

    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        if self.problem.is_some() {
            return;
        }
        if *self.remaining == 0 || self.depth >= 128 {
            self.problem = Some("shadow source pattern inventory exceeds its shared bound".into());
            return;
        }
        *self.remaining -= 1;
        self.depth += 1;
        intravisit::walk_pat(self, pattern);
        self.depth -= 1;
    }

    fn visit_stmt(&mut self, statement: &'tcx hir::Stmt<'tcx>) {
        if self.problem.is_some() {
            return;
        }
        if *self.remaining == 0 {
            self.problem = Some("source statement inventory exceeds the shared graph bound".into());
            return;
        }
        *self.remaining -= 1;
        if matches!(statement.kind, hir::StmtKind::Item(_)) {
            self.problem =
                Some("nested native items need a separate complete shadow root inventory".into());
            return;
        }
        intravisit::walk_stmt(self, statement);
    }
}
