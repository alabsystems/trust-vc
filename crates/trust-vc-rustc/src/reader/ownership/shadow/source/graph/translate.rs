//! Live native source -> owned whole-program data, without ownership admission.
//!
//! Every emitted role retains its original compiler allocation on this stack.
//! This module deliberately cannot turn a Program or a successful structural
//! walk into NativeOwnership. Missing source forms/frames refuse; native
//! expression/scope/region/option correspondence and actual borrowck remain
//! mandatory later stages.

use super::*;
use crate::reader::modes::{AccessKind, AdjustmentKind, VarErasure};
use crate::reader::ownership::shadow::program as out;
use rustc_ast::{BindingMode, ByRef, LitKind};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::PatKind;
use std::collections::BTreeMap;

mod structs;
#[cfg(test)]
mod tests;

/// Original values never leave the original compiler thread. This map is
/// independent of generated names/ranges and must be joined to fresh actual
/// AST/HIR/type/scope roles before a native result can be consumed.
pub(in crate::reader::ownership::shadow) enum Origin<'tcx> {
    Function(LocalDefId),
    Declaration(LocalDefId),
    Variant(DefId),
    Field {
        source: DefId,
        ty: TypeId,
    },
    /// Exact typed place prefixes are not invented expression-mode rows.
    Place {
        source: &'tcx hir::Expr<'tcx>,
        access: AccessKind,
        native: ty::Ty<'tcx>,
        target: out::Type,
        environment: ty::TypingEnv<'tcx>,
    },
    Binding {
        pattern: &'tcx hir::Pat<'tcx>,
        ty: TypeId,
    },
    Expression {
        source: &'tcx hir::Expr<'tcx>,
        expected: Mode,
        result: Mode,
        native: ty::Ty<'tcx>,
        target: out::Type,
    },
    Pattern(&'tcx hir::Pat<'tcx>),
    Arm(&'tcx hir::Arm<'tcx>),
    Generated {
        source: &'tcx hir::Expr<'tcx>,
        rule: GeneratedRule,
        target: out::Type,
    },
    Auxiliary(out::AuxiliaryKind),
}

pub(in crate::reader::ownership::shadow) enum GeneratedRule {
    ControlBoolean,
    RetainedCallBeforeErasure,
    RetainedReadBeforeErasure,
    ShortCircuitBeforeErasure,
    TemporaryScope,
}

/// A cohesive preparation result, not a completed producer. In particular,
/// its owned program is private and no native worker or admission is wired.
pub(in crate::reader::ownership::shadow) struct Mapped<'cx, 'tcx> {
    graph: LiveGraph<'cx, 'tcx>,
    program: out::Program,
    origins: BTreeMap<out::Site, Origin<'tcx>>,
    functions: HashMap<LocalDefId, out::FunctionId>,
    /// These are obligations, never a flag permitting later stages to skip
    /// missing native correspondence or borrow checking.
    unresolved: Vec<String>,
}

impl<'cx, 'tcx> LiveGraph<'cx, 'tcx> {
    pub(in crate::reader::ownership::shadow) fn translate(
        self,
    ) -> Result<Mapped<'cx, 'tcx>, String> {
        self.revalidate()?;
        let mut walk = Walk {
            graph: &self,
            next_site: 0,
            next_local: 0,
            origins: BTreeMap::new(),
            functions: HashMap::new(),
            root_positions: HashMap::new(),
            locals: HashMap::new(),
            local_types: HashMap::new(),
            need_observer: false,
            uses: HashSet::new(),
            arguments: HashSet::new(),
            operations: HashSet::new(),
            adjustments: HashSet::new(),
        };
        for (index, root) in self.roots.iter().enumerate() {
            walk.spend(0)?;
            walk.root_positions.insert(root.source.definition, index);
            let id =
                out::FunctionId(u32::try_from(index).map_err(|_| "source function ID overflow")?);
            if walk.functions.insert(root.source.definition, id).is_some() {
                return Err("a source function occurs twice in the closed program".into());
            }
        }
        let mut adts = Vec::new();
        for (index, declaration) in self.declarations.iter().enumerate() {
            walk.spend(0)?;
            let frame = self
                .frames
                .get(&declaration.source)
                .ok_or("a source ADT has no native generic frame")?;
            walk.frame(frame)?;
            let mut variants = Vec::new();
            for variant in &declaration.variants {
                let mut fields = Vec::new();
                for field in &variant.fields {
                    let site = walk.site(Origin::Field {
                        source: field.source,
                        ty: field.ty,
                    })?;
                    fields.push(out::Field {
                        site,
                        ty: walk.ty(field.ty, 0)?,
                    });
                }
                variants.push(out::Variant {
                    site: walk.site(Origin::Variant(variant.source))?,
                    fields,
                });
            }
            adts.push(out::Adt {
                site: walk.site(Origin::Declaration(declaration.source))?,
                id: out::AdtId(u32::try_from(index).map_err(|_| "source ADT ID overflow")?),
                kind: if declaration.is_enum {
                    out::AdtKind::Enum
                } else {
                    out::AdtKind::Struct
                },
                generics: frame.type_parameters.iter().map(|(_, id)| *id).collect(),
                variants,
            });
        }
        let mut functions = Vec::new();
        for root in &self.roots {
            walk.spend(0)?;
            let frame = self
                .frames
                .get(&root.source.definition)
                .ok_or("a source function has no native generic frame")?;
            walk.frame(frame)?;
            let mut parameters = Vec::new();
            for (parameter, (_, ty)) in root.source.body.params.iter().zip(&root.parameters) {
                parameters.push(walk.binding(root, parameter.pat, *ty)?);
            }
            let body = walk.expr(
                root,
                root.source.body.value,
                Some(root.source.signature.result.mode),
                0,
            )?;
            functions.push(out::Function {
                site: walk.site(Origin::Function(root.source.definition))?,
                id: walk.functions[&root.source.definition],
                generics: frame.type_parameters.iter().map(|(_, id)| *id).collect(),
                regions: Vec::new(),
                parameters,
                result: walk.ty(root.result, 0)?,
                body,
            });
        }
        for root in &self.roots {
            for usage in &root.source.uses {
                walk.spend(0)?;
                if !walk.uses.contains(&(usage.place, usage.access)) {
                    return Err(
                        "a live native availability use was not represented in the whole program"
                            .into(),
                    );
                }
            }
            for argument in &root.source.arguments {
                walk.spend(0)?;
                if !walk.arguments.contains(&(argument.call, argument.position)) {
                    return Err("a live native argument/erasure occurrence was not mapped".into());
                }
            }
            for operation in &root.source.operations {
                walk.spend(0)?;
                if !walk.operations.contains(&operation.expression) {
                    return Err("a live native assignment/borrow operation was not mapped".into());
                }
            }
            for adjustment in &root.source.adjustments {
                walk.spend(0)?;
                if !walk.adjustments.contains(&adjustment.expression) {
                    return Err("a live native adjustment/scope occurrence was not mapped".into());
                }
            }
        }
        let auxiliaries = if walk.need_observer {
            vec![out::Auxiliary {
                site: walk.site(Origin::Auxiliary(out::AuxiliaryKind::ErasedValue))?,
                kind: out::AuxiliaryKind::ErasedValue,
            }]
        } else {
            Vec::new()
        };
        let origins = walk.origins;
        let function_map = walk.functions;
        // `Program::emit` and native::observe are intentionally NOT called.
        let program = out::Program {
            adts,
            functions,
            builtin: None,
            auxiliaries,
        };
        let mut remaining = self.remaining_work.get();
        let emitted_roles = program.validate_with_work(&mut remaining)?;
        self.remaining_work.set(remaining);
        if emitted_roles.len() != origins.len()
            || emitted_roles.iter().any(|site| !origins.contains_key(site))
        {
            return Err(
                "the owned program and actual source/generated role inventories differ".into(),
            );
        }
        self.revalidate()?;
        let mut unresolved = self.requirements.clone();
        unresolved.extend([
            "fresh native expression/pattern/call/field/scope roles must close against every live origin, not generated spelling or byte ranges".into(),
            "original invocation/options/CStore cohorts and full original/native predicates and region relations require a production coordinator".into(),
            "all original availability/shadow/reset/two-phase-loan operations must be represented and rejoined before actual whole-program MIR borrowck can admit any owner".into(),
        ]);
        Ok(Mapped {
            graph: self,
            program,
            origins,
            functions: function_map,
            unresolved,
        })
    }
}

struct Walk<'g, 'cx, 'tcx> {
    graph: &'g LiveGraph<'cx, 'tcx>,
    next_site: u32,
    next_local: u32,
    origins: BTreeMap<out::Site, Origin<'tcx>>,
    functions: HashMap<LocalDefId, out::FunctionId>,
    root_positions: HashMap<LocalDefId, usize>,
    locals: HashMap<HirId, out::LocalId>,
    local_types: HashMap<HirId, TypeId>,
    need_observer: bool,
    uses: HashSet<(HirId, AccessKind)>,
    arguments: HashSet<(HirId, usize)>,
    operations: HashSet<HirId>,
    adjustments: HashSet<HirId>,
}

impl<'tcx> Walk<'_, '_, 'tcx> {
    fn spend(&self, depth: usize) -> Result<(), String> {
        if depth >= 128 {
            return Err("source/program mapping exceeds its depth bound".into());
        }
        let next = self
            .graph
            .remaining_work
            .get()
            .checked_sub(1)
            .ok_or("source/program mapping exhausts the SAME whole-program work ledger")?;
        self.graph.remaining_work.set(next);
        Ok(())
    }
    fn synthetic_site(&mut self) -> Result<out::Site, String> {
        self.spend(0)?;
        let site = out::Site(self.next_site);
        self.next_site = self
            .next_site
            .checked_add(1)
            .ok_or("source site identity overflow")?;
        Ok(site)
    }
    fn site(&mut self, source: Origin<'tcx>) -> Result<out::Site, String> {
        let site = self.synthetic_site()?;
        if self.origins.insert(site, source).is_some() {
            return Err("duplicate source/program site".into());
        }
        Ok(site)
    }
    fn frame(&self, frame: &Frame<'tcx>) -> Result<(), String> {
        self.spend(0)?;
        if frame.inherited_parent.is_some()
            || !frame.regions.is_empty()
            || !frame.constants.is_empty()
        {
            return Err("source inherited/region/const frames need a complete native binder/relationship map; no new lifetime or type substitution is invented".into());
        }
        // Predicate data remains in the live graph. This preparation grants
        // no native declaration, bound, Copy fact or callable equation.
        Ok(())
    }
    fn ty(&self, id: TypeId, depth: usize) -> Result<out::Type, String> {
        self.spend(depth)?;
        let node = self
            .graph
            .types
            .get(id.0)
            .ok_or("a target type lacks its actual position-aware source node")?;
        Ok(match &node.shape {
            Shape::ErasedUnit | Shape::Unit => out::Type::Unit,
            Shape::Bool => out::Type::Bool,
            Shape::Signed(kind) => out::Type::Signed(*kind),
            Shape::Unsigned(kind) => out::Type::Unsigned(*kind),
            Shape::Never => out::Type::Never,
            Shape::Parameter { target, .. } => out::Type::Parameter(*target),
            Shape::Tuple(fields) => out::Type::Tuple(fields.iter().map(|id| self.ty(*id, depth + 1)).collect::<Result<_,_>>()?),
            Shape::Adt { declaration, arguments } => out::Type::Adt(
                out::AdtId(u32::try_from(declaration.0).map_err(|_| "target ADT identity overflow")?),
                arguments.iter().map(|id| self.ty(*id, depth + 1)).collect::<Result<_,_>>()?),
            Shape::Reference { .. } => return Err("a retained native reference requires its exact bound/region/outlives and owned-resolution map, not an invented target lifetime".into()),
            Shape::Pending => return Err("an unfinished native type node cannot become program data".into()),
            Shape::Unmaterialized(reason) => return Err(reason.clone()),
        })
    }
    fn type_id(
        &self,
        root: &RootPlan<'tcx>,
        original: ty::Ty<'tcx>,
        position: Position,
    ) -> Result<TypeId, String> {
        self.spend(0)?;
        self.graph
            .type_ids
            .get(&(original, root.source.definition, position.key()))
            .copied()
            .ok_or("an actual source type/position was not closed in the live graph".into())
    }
    fn binding(
        &mut self,
        root: &RootPlan<'tcx>,
        pattern: &'tcx hir::Pat<'tcx>,
        id: TypeId,
    ) -> Result<out::Binding, String> {
        self.spend(0)?;
        let hir::PatKind::Binding(BindingMode(ByRef::No, mutability), binding, _, None) =
            pattern.kind
        else {
            return Err("source binding needs the actual by-value native pattern".into());
        };
        let mode = root.source.checked.bindings.mode_for(
            root.source.tcx,
            root.source.definition,
            root.source.definition,
            root.source.body,
            pattern,
        )?;
        let node = self.graph.types.get(id.0).ok_or("binding type absent")?;
        if node.original != root.source.typeck.pat_ty(pattern)
            || node.owner != root.source.definition
        {
            return Err("binding lost its current native type/owner join".into());
        }
        let expected = match node.position {
            Position::Parameter(m) | Position::Storage(m) => m,
            _ => return Err("binding type has a foreign position".into()),
        };
        if mode != expected || binding != pattern.hir_id || self.locals.contains_key(&binding) {
            return Err("binding lost its exact unique native mode/pattern join".into());
        }
        let local = out::LocalId(self.next_local);
        self.next_local = self
            .next_local
            .checked_add(1)
            .ok_or("native local mapping exhausted")?;
        self.locals.insert(binding, local);
        self.local_types.insert(binding, id);
        Ok(out::Binding {
            site: self.site(Origin::Binding { pattern, ty: id })?,
            id: local,
            ty: self.ty(id, 0)?,
            mutable: mutability.is_mut(),
        })
    }
    fn observed(
        &mut self,
        root: &RootPlan<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
        expected: Option<Mode>,
    ) -> Result<(Mode, Mode), String> {
        self.spend(0)?;
        let rows = root.source.checked.expressions.for_expression(
            root.source.tcx,
            root.source.definition,
            root.source.definition,
            expression,
        )?;
        let mut selected = rows
            .iter()
            .filter(|row| expected.is_none_or(|mode| mode == row.context.expected));
        let row = selected
            .next()
            .ok_or("source expression lacks its exact expected native mode observation")?;
        if selected.next().is_some() {
            return Err(
                "source expression has ambiguous native contexts; no context is guessed".into(),
            );
        }
        let native_adjustments = root.source.typeck.expr_adjustments(expression);
        // Rust can record NeverToAny even when both types are exactly `!`.
        // Keep that use only when the original checker saw the same occurrence
        // and the native adjustment cannot change the target type or loans.
        let never_identity = matches!(native_adjustments, [adjustment]
            if matches!(adjustment.kind, ty::adjustment::Adjust::NeverToAny)
                && row.native_type.is_never()
                && adjustment.target == row.native_type
                && row.adjusted_type == row.native_type);
        if !native_adjustments.is_empty() && !never_identity {
            return Err(
                "native adjustments/reborrows need their whole-call and two-phase mapping".into(),
            );
        }
        if root.adjustment_ids.contains(&expression.hir_id) {
            let adjustment = root
                .source
                .checked
                .availability
                .adjustment_for(expression)?;
            let expected: &[_] = if never_identity {
                &[AdjustmentKind::NeverToAny]
            } else {
                &[]
            };
            if adjustment.kinds.as_slice() != expected || adjustment.reborrow.is_some() {
                return Err(
                    "a captured native adjustment/reborrow has no complete target mapping".into(),
                );
            }
            self.adjustments.insert(expression.hir_id);
        } else if never_identity {
            return Err("the original never adjustment has no checked availability row".into());
        }
        Ok((row.result, row.context.expected))
    }
    fn observe(&mut self, reads: Vec<out::Expr>, result: out::Inhabited) -> out::ExprKind {
        self.need_observer = true;
        out::ExprKind::Observe { reads, result }
    }
    fn expr(
        &mut self,
        root: &RootPlan<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
        expected: Option<Mode>,
        depth: usize,
    ) -> Result<out::Expr, String> {
        self.spend(depth)?;
        let tcx = root.source.tcx;
        let (mode, expected) = self.observed(root, expression, expected)?;
        let native = root.source.typeck.expr_ty_adjusted(expression);
        let ty = self.ty(self.type_id(root, native, Position::Value(mode))?, 0)?;
        let erase = mode == Mode::Spec || expected == Mode::Spec;
        let kind = match expression.kind {
            hir::ExprKind::Lit(lit) => match lit.node {
                LitKind::Bool(value) if !erase => out::ExprKind::Bool(value),
                LitKind::Bool(_) if erase => self.observe(Vec::new(), out::Inhabited::Unit),
                LitKind::Int(value, _) if !erase => out::ExprKind::Integer { magnitude: value.get(), ty: ty.clone() },
                LitKind::Int(..) if erase => self.observe(Vec::new(), out::Inhabited::Unit),
                _ => return Err("literal needs a first-class source/program representation".into()),
            },
            hir::ExprKind::Path(ref path) => {
                let Res::Local(binding) = root.source.typeck.qpath_res(path, expression.hir_id) else { return Err("a value path needs its actual local/constructor role".into()); };
                let usage = root.source.checked.availability.use_for(expression, AccessKind::Read)?;
                if usage.binding != binding || usage.local_use != expression.hir_id || usage.place != expression.hir_id { return Err("local read lost its exact availability/source binding".into()); }
                self.uses.insert((usage.place,usage.access));
                match usage.erasure {
                    VarErasure::Keep => {
                        let kind=out::ExprKind::Local(*self.locals.get(&binding).ok_or("kept read lacks actual mapped storage")?);
                        if erase {
                            let site=self.site(Origin::Generated {source:expression,rule:GeneratedRule::RetainedReadBeforeErasure,target:ty.clone()})?;
                            self.observe(vec![out::Expr {site,kind}],out::Inhabited::Unit)
                        } else {kind}
                    },
                    VarErasure::Erase if erase => self.observe(Vec::new(), out::Inhabited::Unit),
                    VarErasure::Erase => return Err("erased availability read cannot supply a retained target value".into()),
                    VarErasure::Shadow => return Err("a tracked Spec observation needs actual separate shadow storage, assignment resets and loan/scoped-use correspondence; it is never silently dropped".into()),
                }
            }
            hir::ExprKind::Tup(values) => {
                let mut fields = Vec::new();
                for (position, value) in values.iter().enumerate() {
                    self.spend(depth + 1)?;
                    let argument = root.source.checked.availability.argument_for(expression, position)?;
                    if argument.argument != value.hir_id || argument.mode != Mode::Exec || argument.erased {
                        return Err("a tuple element changed its original argument or erasure mode".into());
                    }
                    self.arguments.insert((argument.call, argument.position));
                    fields.push(self.expr(root, value, None, depth + 1)?);
                }
                if erase { self.observe(fields, out::Inhabited::Unit) } else if values.is_empty() { out::ExprKind::Unit } else { out::ExprKind::Tuple(fields) }
            }
            hir::ExprKind::Block(block, None) => {
                let mut statements = Vec::new();
                for statement in block.stmts {
                    self.spend(depth + 1)?;
                    match statement.kind {
                        hir::StmtKind::Let(local) => {
                            if local.els.is_some() { return Err("let-else needs its complete control/scope map".into()); }
                            let binding_ty = root.bindings.get(&local.pat.hir_id).ok_or("source Let lacks its exact completed binding/type row")?;
                            let mode = root.source.checked.bindings.mode_for(tcx, root.source.definition, root.source.definition, root.source.body, local.pat)?;
                            let initializer = local.init.map(|value| self.expr(root, value, Some(mode), depth + 1)).transpose()?;
                            let binding = self.binding(root, local.pat, *binding_ty)?;
                            statements.push(out::Statement::Let { binding, initializer });
                        }
                        hir::StmtKind::Expr(value) | hir::StmtKind::Semi(value) => statements.push(out::Statement::Expression(self.expr(root, value, None, depth + 1)?)),
                        hir::StmtKind::Item(_) => return Err("a nested item cannot be smuggled into a mapped native body".into()),
                    }
                }
                let tail = block.expr.map(|value| self.expr(root,value,Some(expected),depth+1).map(Box::new)).transpose()?;
                out::ExprKind::Block { statements, tail }
            }
            hir::ExprKind::DropTemps(_) => return Err("DropTemps requires an exact original/native temporary-scope correspondence; it is not stripped or replaced by an invented block".into()),
            hir::ExprKind::If(condition, yes, no) => {
                let condition = self.boolean(root, condition, depth + 1)?;
                let then_value = self.expr(root, yes, Some(expected), depth + 1)?;
                let else_value = no.map(|value| self.expr(root,value,Some(expected),depth+1)).transpose()?.ok_or("a missing else needs its explicit Unit/source-scope role")?;
                out::ExprKind::If { condition:Box::new(condition),then_value:Box::new(then_value),else_value:Box::new(else_value) }
            }
            hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Normal) => {
                let facts = root.source.checked.matches.for_match(tcx,root.source.definition,root.source.definition,root.source.typeck,expression,scrutinee,arms)?;
                if facts.scrutinee_mode == Mode::Spec && !root.source.typeck.expr_ty_adjusted(scrutinee).is_bool() { return Err("a Spec nominal match needs a genuinely inhabited variant-choice/control representation".into()); }
                let scrutinee = if facts.scrutinee_mode == Mode::Spec { self.boolean(root,scrutinee,depth+1)? } else { self.expr(root,scrutinee,None,depth+1)? };
                let mut mapped = Vec::new();
                for arm in arms {
                    if arm.guard.is_some() { return Err("guarded native Match needs complete guard scope/effect mapping".into()); }
                    let pattern = self.pattern(root,arm.pat,depth+1)?;
                    let body = self.expr(root,arm.body,Some(expected),depth+1)?;
                    mapped.push(out::Arm { site:self.site(Origin::Arm(arm))?,pattern,body });
                }
                out::ExprKind::Match { scrutinee:Box::new(scrutinee),arms:mapped }
            }
            hir::ExprKind::Ret(value) => out::ExprKind::Return(value.map(|value|self.expr(root,value,Some(root.source.signature.result.mode),depth+1).map(Box::new)).transpose()?),
            hir::ExprKind::Call(callee, values) => self.call(root,expression,callee,values,erase,ty.clone(),depth+1)?,
            hir::ExprKind::Struct(ref path, fields, tail) => {
                self.struct_expression(root, expression, path, fields, tail, erase, depth + 1)?
            }
            hir::ExprKind::Field(..) => {
                self.field_expression(root, expression, mode, erase, depth + 1)?
            }
            hir::ExprKind::Assign(place,value,_) => {
                let operation = root.source.checked.availability.operation_for(expression)?;
                let access = root.source.checked.availability.use_for(place,AccessKind::Assign)?;
                if operation.place != place.hir_id || operation.mode != access.mode || operation.place_mode != access.place_mode || operation.kind != AccessKind::Assign { return Err("source assignment lost its native operation/place modes".into()); }
                if matches!(place.kind, hir::ExprKind::Field(..)) {
                    self.field_assignment(root, expression, place, value, depth + 1)?
                } else {
                let hir::ExprKind::Path(ref path) = place.kind else { return Err("projected assignment needs its exact target place/scope/loan mapping".into()); };
                let Res::Local(binding) = root.source.typeck.qpath_res(path,place.hir_id) else { return Err("assignment target is not an actual local".into()); };
                if binding != access.binding { return Err("assignment native binding mismatch".into()); }
                self.uses.insert((access.place,access.access));
                self.operations.insert(operation.expression);
                if root.adjustment_ids.contains(&place.hir_id) {
                    let adjustment=root.source.checked.availability.adjustment_for(place)?;
                    if !adjustment.kinds.is_empty() || adjustment.reborrow.is_some() || !root.source.typeck.expr_adjustments(place).is_empty() {return Err("assignment place adjustment needs its native loan map".into());}
                    self.adjustments.insert(place.hir_id);
                }
                let value = self.expr(root,value,Some(operation.place_mode),depth+1)?;
                out::ExprKind::Assign { destination:*self.locals.get(&binding).ok_or("assignment lacks actual mapped local")?,value:Box::new(value) }
                }
            }
            hir::ExprKind::Unary(op,value) => {
                if !primitive(root.source.typeck.expr_ty_adjusted(value)) {return Err("overloaded unary operation needs its exact native instance/call mapping".into());}
                if op==hir::UnOp::Neg && matches!(value.kind,hir::ExprKind::Lit(_)) {return Err("a negated literal needs its exact signed-boundary literal composition map".into());}
                let value = self.expr(root,value,None,depth+1)?;
                if erase { self.observe(vec![value],out::Inhabited::Unit) } else {
                    out::ExprKind::Unary { op:match op { hir::UnOp::Not=>out::Unary::Not,hir::UnOp::Neg=>out::Unary::Neg,hir::UnOp::Deref=>return Err("dereference needs complete region/owned-place correspondence".into()) },value:Box::new(value) }
                }
            }
            hir::ExprKind::Binary(op,left,right) => {
                if !primitive(root.source.typeck.expr_ty_adjusted(left)) || !primitive(root.source.typeck.expr_ty_adjusted(right)) {return Err("overloaded/nonprimitive binary operation needs its exact native call/layout mapping".into());}
                if matches!(op.node,rustc_hir::BinOpKind::And|rustc_hir::BinOpKind::Or) {
                    let left=self.boolean(root,left,depth+1)?;let right=self.boolean(root,right,depth+1)?;
                    let binary=out::ExprKind::Binary { op:if op.node==rustc_hir::BinOpKind::And {out::Binary::And}else{out::Binary::Or},left:Box::new(left),right:Box::new(right) };
                    if erase { let inner=out::Expr {site:self.site(Origin::Generated {source:expression,rule:GeneratedRule::ShortCircuitBeforeErasure,target:out::Type::Bool})?,kind:binary};self.observe(vec![inner],out::Inhabited::Unit) } else {binary}
                } else {
                    let left=self.expr(root,left,None,depth+1)?;let right=self.expr(root,right,None,depth+1)?;
                    if erase {self.observe(vec![left,right],out::Inhabited::Unit)} else {out::ExprKind::Binary {op:binary(op.node)?,left:Box::new(left),right:Box::new(right)}}
                }
            }
            _ => return Err("native expression needs a complete explicit owned representation; no raw source/type fallback is available".into()),
        };
        let target = if matches!(expression.kind, hir::ExprKind::Ret(_)) {
            out::Type::Never
        } else if erase {
            out::Type::Unit
        } else {
            ty
        };
        Ok(out::Expr {
            site: self.site(Origin::Expression {
                source: expression,
                expected,
                result: mode,
                native,
                target,
            })?,
            kind,
        })
    }
    fn boolean(
        &mut self,
        root: &RootPlan<'tcx>,
        source: &'tcx hir::Expr<'tcx>,
        depth: usize,
    ) -> Result<out::Expr, String> {
        self.spend(depth)?;
        if !root.source.typeck.expr_ty_adjusted(source).is_bool() {
            return Err("control has no actual native Bool type".into());
        }
        if let hir::ExprKind::DropTemps(inner) = source.kind {
            let actual = root
                .condition_scopes
                .get(&source.hir_id)
                .is_some_and(|condition| std::ptr::eq(*condition, source));
            if !actual
                || !matches!(root.source.tcx.hir_node(source.hir_id),hir::Node::Expr(current) if std::ptr::eq(current,source))
            {
                return Err("a condition wrapper lacks its exact native control/scope role".into());
            }
            if !root.source.typeck.expr_adjustments(source).is_empty() {
                return Err(
                    "a control wrapper adjustment needs its complete scope/loan mapping".into(),
                );
            }
            if root.adjustment_ids.contains(&source.hir_id) {
                let adjustment = root.source.checked.availability.adjustment_for(source)?;
                if !adjustment.kinds.is_empty() || adjustment.reborrow.is_some() {
                    return Err("a control wrapper has an unrepresented adjustment".into());
                }
                self.adjustments.insert(source.hir_id);
            }
            let value = self.boolean(root, inner, depth + 1)?;
            let site = self.site(Origin::Generated {
                source,
                rule: GeneratedRule::TemporaryScope,
                target: out::Type::Bool,
            })?;
            return Ok(out::Expr {
                site,
                kind: out::ExprKind::TemporaryScope(Box::new(value)),
            });
        }
        let (mode, expected) = self.observed(root, source, None)?;
        let value = self.expr(root, source, Some(expected), depth + 1)?;
        if mode != Mode::Spec && expected != Mode::Spec {
            return Ok(value);
        }
        let site = self.site(Origin::Generated {
            source,
            rule: GeneratedRule::ControlBoolean,
            target: out::Type::Bool,
        })?;
        Ok(out::Expr {
            site,
            kind: self.observe(vec![value], out::Inhabited::Bool),
        })
    }
    fn call(
        &mut self,
        root: &RootPlan<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
        callee: &'tcx hir::Expr<'tcx>,
        values: &'tcx [hir::Expr<'tcx>],
        erase: bool,
        retained_type: out::Type,
        depth: usize,
    ) -> Result<out::ExprKind, String> {
        self.spend(depth)?;
        let graph = self.graph;
        let call = root
            .call_positions
            .get(&expression.hir_id)
            .and_then(|index| root.source.calls.get(*index))
            .ok_or("actual call is missing from the complete source closure")?;
        if !std::ptr::eq(call.expression, expression) {
            return Err("call index changed source allocation".into());
        }
        if !std::ptr::eq(call.callee, callee) || !std::ptr::eq(call.values, values) {
            return Err("actual source call allocation/argument slice changed".into());
        }
        if !root.source.typeck.expr_adjustments(callee).is_empty() {
            return Err("an adjusted callee needs its exact native callable mapping".into());
        }
        if root.adjustment_ids.contains(&callee.hir_id) {
            let adjustment = root.source.checked.availability.adjustment_for(callee)?;
            if !adjustment.kinds.is_empty() || adjustment.reborrow.is_some() {
                return Err("a callee adjustment is not represented".into());
            }
            self.adjustments.insert(callee.hir_id);
        }
        if matches!(root.source.tcx.def_kind(call.target), DefKind::Ctor(..)) {
            let native = root.source.typeck.expr_ty(expression);
            let ty::Adt(definition, _) = native.kind() else {
                return Err("constructor lost its actual native result datatype".into());
            };
            let hir::ExprKind::Path(ref path) = callee.kind else {
                return Err("constructor lacks actual native path resolution".into());
            };
            let resolution = root.source.typeck.qpath_res(path, callee.hir_id);
            if !matches!(resolution, Res::Def(DefKind::Ctor(..), target) if target == call.target) {
                return Err("a constructor call changed its actual resolved native target".into());
            }
            let (variant, actual) =
                crate::reader::datatypes::constructor_variant(*definition, resolution)
                    .ok_or("constructor lost actual native variant identity")?;
            let declaration = *self
                .graph
                .declaration_ids
                .get(
                    &definition
                        .did()
                        .as_local()
                        .ok_or("foreign constructor has no source declaration")?,
                )
                .ok_or("constructor declaration was not closed")?;
            let plan = &graph.declarations[declaration.0];
            let variant_plan = plan
                .variants
                .get(variant as usize)
                .ok_or("native variant index outside its complete declaration")?;
            if plan.is_enum != definition.is_enum()
                || variant_plan.source != actual.def_id
                || variant_plan.fields.len() != values.len()
            {
                return Err("constructor variant/field inventory mismatch".into());
            }
            let mut fields = Vec::new();
            for (position, (value, field)) in values.iter().zip(&variant_plan.fields).enumerate() {
                let argument = root
                    .source
                    .checked
                    .availability
                    .argument_for(expression, position)?;
                if argument.argument != value.hir_id
                    || argument.mode != field.mode
                    || argument.erased != (field.mode == Mode::Spec)
                {
                    return Err("constructor argument lost exact native field mode/erasure".into());
                }
                self.arguments.insert((argument.call, argument.position));
                fields.push(self.expr(root, value, Some(field.mode), depth + 1)?);
            }
            let types = root
                .call_types
                .get(&expression.hir_id)
                .ok_or("constructor type frame is missing")?
                .iter()
                .map(|id| self.ty(*id, 0))
                .collect::<Result<_, _>>()?;
            let target_type = self.ty(
                *root
                    .construction_types
                    .get(&expression.hir_id)
                    .ok_or("constructor lacks its closed retained type requirement")?,
                0,
            )?;
            let adt = out::AdtId(
                u32::try_from(declaration.0).map_err(|_| "constructor ADT ID overflow")?,
            );
            let kind = if plan.is_enum {
                out::ExprKind::Construct {
                    adt,
                    variant: variant as usize,
                    types,
                    fields,
                }
            } else {
                if variant != 0 || plan.variants.len() != 1 {
                    return Err(
                        "a native struct constructor has a different non-enum variant".into(),
                    );
                }
                let ty::Adt(_, actual_arguments) = native.kind() else {
                    unreachable!()
                };
                if call.arguments.len() != actual_arguments.len() {
                    return Err(
                        "a struct constructor lost its full actual native argument vector".into(),
                    );
                }
                for (call_argument, actual_argument) in
                    call.arguments.iter().zip(actual_arguments.iter())
                {
                    self.spend(depth + 1)?;
                    if call_argument != actual_argument {
                        return Err(
                            "a struct constructor changed its ordered native type arguments".into(),
                        );
                    }
                }
                self.corresponding_type(root, native, &target_type, depth + 1)?;
                let mut ordered_fields = Vec::new();
                for (position, field) in fields.into_iter().enumerate() {
                    self.spend(depth + 1)?;
                    ordered_fields.push((position, field));
                }
                out::ExprKind::ConstructStruct {
                    adt,
                    types,
                    fields: ordered_fields,
                }
            };
            return if erase {
                let site = self.site(Origin::Generated {
                    source: expression,
                    rule: GeneratedRule::RetainedCallBeforeErasure,
                    target: target_type,
                })?;
                Ok(self.observe(vec![out::Expr { site, kind }], out::Inhabited::Unit))
            } else {
                Ok(kind)
            };
        }
        let source_target = call.target.as_local().ok_or(
            "foreign call requires genuine target/cohort semantics; it is not erased by name",
        )?;
        let target = self
            .root_positions
            .get(&source_target)
            .and_then(|index| self.graph.roots.get(*index))
            .ok_or("call target body is not in the closed live graph")?;
        if values.len() != target.source.signature.parameters.len() {
            return Err("source call signature/argument count mismatch".into());
        }
        let mut arguments = Vec::new();
        for (position, (value, (_, formal))) in values
            .iter()
            .zip(&target.source.signature.parameters)
            .enumerate()
        {
            let actual = root
                .source
                .checked
                .availability
                .argument_for(expression, position)?;
            if actual.argument != value.hir_id
                || actual.mode != formal.mode
                || actual.erased != (formal.mode == Mode::Spec)
            {
                return Err("call argument lost actual native formal/erasure context".into());
            }
            self.arguments.insert((actual.call, actual.position));
            arguments.push(self.expr(root, value, Some(formal.mode), depth + 1)?);
        }
        let types = root
            .call_types
            .get(&expression.hir_id)
            .ok_or("actual call type frame is missing")?
            .iter()
            .map(|id| self.ty(*id, 0))
            .collect::<Result<_, _>>()?;
        let kind = out::ExprKind::Call {
            function: *self
                .functions
                .get(&source_target)
                .ok_or("closed call has no target identity")?,
            types,
            arguments,
        };
        if erase {
            let site = self.site(Origin::Generated {
                source: expression,
                rule: GeneratedRule::RetainedCallBeforeErasure,
                target: retained_type,
            })?;
            Ok(self.observe(vec![out::Expr { site, kind }], out::Inhabited::Unit))
        } else {
            Ok(kind)
        }
    }
    fn pattern(
        &mut self,
        root: &RootPlan<'tcx>,
        pattern: &'tcx hir::Pat<'tcx>,
        depth: usize,
    ) -> Result<out::Pattern, String> {
        self.spend(depth)?;
        let tcx = root.source.tcx;
        if !matches!(tcx.hir_node(pattern.hir_id),hir::Node::Pat(current) if std::ptr::eq(current,pattern))
        {
            return Err("pattern lost actual native allocation".into());
        }
        let kind = match pattern.kind {
            PatKind::Wild => out::PatternKind::Wild,
            PatKind::Binding(..) => {
                let ty = root
                    .bindings
                    .get(&pattern.hir_id)
                    .ok_or("pattern binding lacks completed native mode/type")?;
                out::PatternKind::Binding(self.binding(root, pattern, *ty)?)
            }
            PatKind::Tuple(fields, _) => {
                let ty::Tuple(types) = root.source.typeck.pat_ty(pattern).kind() else {
                    return Err("tuple pattern lost native tuple type".into());
                };
                if fields.len() != types.len() {
                    return Err("tuple-rest pattern needs its full slot map".into());
                }
                out::PatternKind::Tuple(
                    fields
                        .iter()
                        .map(|field| self.pattern(root, field, depth + 1))
                        .collect::<Result<_, _>>()?,
                )
            }
            PatKind::TupleStruct(ref path, fields, _) => {
                let ty::Adt(definition, _) = root.source.typeck.pat_ty(pattern).kind() else {
                    return Err("variant pattern has no actual datatype".into());
                };
                let resolution = root.source.typeck.qpath_res(path, pattern.hir_id);
                let (variant, actual) =
                    crate::reader::datatypes::constructor_variant(*definition, resolution)
                        .ok_or("pattern lost actual native variant identity")?;
                let declaration = *self
                    .graph
                    .declaration_ids
                    .get(
                        &definition
                            .did()
                            .as_local()
                            .ok_or("foreign pattern declaration")?,
                    )
                    .ok_or("pattern declaration absent from graph")?;
                let plan = &self.graph.declarations[declaration.0];
                if !plan.is_enum
                    || plan
                        .variants
                        .get(variant as usize)
                        .is_none_or(|v| v.source != actual.def_id || v.fields.len() != fields.len())
                {
                    return Err(
                        "variant/rest pattern requires its exact full field slot map".into(),
                    );
                }
                out::PatternKind::Variant {
                    adt: out::AdtId(
                        u32::try_from(declaration.0).map_err(|_| "pattern ADT ID overflow")?,
                    ),
                    variant: variant as usize,
                    fields: fields
                        .iter()
                        .map(|field| self.pattern(root, field, depth + 1))
                        .collect::<Result<_, _>>()?,
                }
            }
            PatKind::Expr(expr) => match expr.kind {
                hir::PatExprKind::Lit {
                    lit,
                    negated: false,
                } => match lit.node {
                    LitKind::Bool(value) => out::PatternKind::Bool(value),
                    _ => return Err("non-Bool literal pattern needs its native target form".into()),
                },
                _ => return Err("constant/variant pattern needs its actual declaration map".into()),
            },
            _ => {
                return Err("pattern needs complete native field/binding/adjustment mapping".into())
            }
        };
        Ok(out::Pattern {
            site: self.site(Origin::Pattern(pattern))?,
            kind,
        })
    }
}

fn binary(op: hir::BinOpKind) -> Result<out::Binary, String> {
    use hir::BinOpKind as B;
    Ok(match op {
        B::Add => out::Binary::Add,
        B::Sub => out::Binary::Sub,
        B::Mul => out::Binary::Mul,
        B::Div => out::Binary::Div,
        B::Rem => out::Binary::Rem,
        B::And => out::Binary::And,
        B::Or => out::Binary::Or,
        B::BitAnd => out::Binary::BitAnd,
        B::BitOr => out::Binary::BitOr,
        B::BitXor => out::Binary::BitXor,
        B::Shl => out::Binary::Shl,
        B::Shr => out::Binary::Shr,
        B::Eq => out::Binary::Eq,
        B::Ne => out::Binary::Ne,
        B::Lt => out::Binary::Lt,
        B::Le => out::Binary::Le,
        B::Gt => out::Binary::Gt,
        B::Ge => out::Binary::Ge,
    })
}

fn primitive(value: ty::Ty<'_>) -> bool {
    matches!(value.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
}
