//! Live source capture and position-aware native erasure requirements.
//!
//! This graph stays in the original compiler context with its canonical mode
//! Rcs. It is not Send data, a materialized program, or an ownership result.
//! Native declarations, call/control/site/region/predicate/option joins and the
//! actual second-compiler result remain separate mandatory producer stages.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::super::program::{GenericId, Signed, Unsigned};
use super::*;
use rustc_hir::def_id::DefId;
use rustc_span::Span;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

mod translate;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::reader::ownership::shadow) enum Position {
    Parameter(Mode),
    Result(Mode),
    Storage(Mode),
    Value(Mode),
    Field(Mode),
    /// Observation storage keeps the relevant native ownership/lifetime
    /// carrier shape, after genuine field/signature erasure; never native !.
    ShadowStorage,
    /// A Spec condition needs an inhabited bool proxy, not native unit or
    /// a known-diverging original computation which deletes a branch.
    ControlBoolean,
}
impl Position {
    fn key(self) -> u8 {
        fn mode(mode: Mode) -> u8 {
            match mode {
                Mode::Spec => 0,
                Mode::Proof => 1,
                Mode::Exec => 2,
            }
        }
        match self {
            Self::Parameter(m) => mode(m),
            Self::Result(m) => 3 + mode(m),
            Self::Storage(m) => 6 + mode(m),
            Self::Value(m) => 9 + mode(m),
            Self::Field(m) => 12 + mode(m),
            Self::ShadowStorage => 15,
            Self::ControlBoolean => 16,
        }
    }
    fn erases_storage(self) -> bool {
        matches!(
            self,
            Self::Parameter(Mode::Spec)
                | Self::Result(Mode::Spec)
                | Self::Storage(Mode::Spec)
                | Self::Value(Mode::Spec)
                | Self::Field(Mode::Spec)
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::reader::ownership::shadow) struct TypeId(
    pub(in crate::reader::ownership::shadow) usize,
);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::reader::ownership::shadow) struct DeclarationId(
    pub(in crate::reader::ownership::shadow) usize,
);

#[derive(Clone, Debug)]
pub(in crate::reader::ownership::shadow) enum Shape<'tcx> {
    Pending,
    ErasedUnit,
    Unit,
    Bool,
    Signed(Signed),
    Unsigned(Unsigned),
    Never,
    Parameter {
        source: DefId,
        target: GenericId,
    },
    Tuple(Vec<TypeId>),
    Adt {
        declaration: DeclarationId,
        arguments: Vec<TypeId>,
    },
    /// Capture the actual source region without pretending that an erased
    /// region/name is the same region in the independent native compiler.
    Reference {
        region: ty::Region<'tcx>,
        mutable: bool,
        target: TypeId,
    },
    Unmaterialized(String),
}

pub(in crate::reader::ownership::shadow) struct TypeNode<'tcx> {
    pub(in crate::reader::ownership::shadow) original: ty::Ty<'tcx>,
    pub(in crate::reader::ownership::shadow) owner: LocalDefId,
    pub(in crate::reader::ownership::shadow) position: Position,
    pub(in crate::reader::ownership::shadow) shape: Shape<'tcx>,
}
pub(in crate::reader::ownership::shadow) struct Frame<'tcx> {
    pub(in crate::reader::ownership::shadow) owner: LocalDefId,
    original: &'tcx ty::Generics,
    pub(in crate::reader::ownership::shadow) type_parameters: Vec<(DefId, GenericId)>,
    pub(in crate::reader::ownership::shadow) regions: Vec<DefId>,
    pub(in crate::reader::ownership::shadow) constants: Vec<DefId>,
    pub(in crate::reader::ownership::shadow) predicates: Vec<(ty::Clause<'tcx>, Span)>,
    pub(in crate::reader::ownership::shadow) inherited_parent: Option<DefId>,
    parameter_ids: HashSet<DefId>,
    type_targets: HashMap<DefId, GenericId>,
}
pub(in crate::reader::ownership::shadow) struct FieldPlan {
    pub(in crate::reader::ownership::shadow) source: DefId,
    pub(in crate::reader::ownership::shadow) mode: Mode,
    pub(in crate::reader::ownership::shadow) ty: TypeId,
}
pub(in crate::reader::ownership::shadow) struct VariantPlan {
    pub(in crate::reader::ownership::shadow) source: DefId,
    pub(in crate::reader::ownership::shadow) fields: Vec<FieldPlan>,
}
pub(in crate::reader::ownership::shadow) struct DeclarationPlan {
    pub(in crate::reader::ownership::shadow) source: LocalDefId,
    pub(in crate::reader::ownership::shadow) is_enum: bool,
    pub(in crate::reader::ownership::shadow) variants: Vec<VariantPlan>,
}
pub(in crate::reader::ownership::shadow) struct RootPlan<'tcx> {
    pub(in crate::reader::ownership::shadow) source: SourceInventory<'tcx>,
    pub(in crate::reader::ownership::shadow) parameters: Vec<(HirId, TypeId)>,
    pub(in crate::reader::ownership::shadow) result: TypeId,
    pub(in crate::reader::ownership::shadow) bindings: HashMap<HirId, TypeId>,
    pub(in crate::reader::ownership::shadow) expressions: Vec<ExpressionPlan<'tcx>>,
    pub(in crate::reader::ownership::shadow) call_types: HashMap<HirId, Vec<TypeId>>,
    call_positions: HashMap<HirId, usize>,
    condition_scopes: HashMap<HirId, &'tcx hir::Expr<'tcx>>,
    construction_types: HashMap<HirId, TypeId>,
    adjustment_ids: HashSet<HirId>,
}

#[derive(Clone, Copy, Debug)]
pub(in crate::reader::ownership::shadow) struct ExpressionContext {
    pub(in crate::reader::ownership::shadow) outer: Mode,
    pub(in crate::reader::ownership::shadow) expected: Mode,
    pub(in crate::reader::ownership::shadow) pure: bool,
    pub(in crate::reader::ownership::shadow) proof_in_spec: bool,
    pub(in crate::reader::ownership::shadow) assert_by: bool,
    pub(in crate::reader::ownership::shadow) block_ghost: bool,
    pub(in crate::reader::ownership::shadow) uses_ghost_blocks: bool,
}
pub(in crate::reader::ownership::shadow) struct ExpressionPlan<'tcx> {
    pub(in crate::reader::ownership::shadow) original: &'tcx hir::Expr<'tcx>,
    pub(in crate::reader::ownership::shadow) context: ExpressionContext,
    pub(in crate::reader::ownership::shadow) result: Mode,
    pub(in crate::reader::ownership::shadow) native_type: TypeId,
    pub(in crate::reader::ownership::shadow) adjusted_type: TypeId,
}

/// One crate/control-graph capture. Original native values remain borrowed
/// here; only a later fully mapped owned program may cross to the worker.
pub(in crate::reader::ownership::shadow) struct LiveGraph<'cx, 'tcx> {
    cx: &'cx Cx<'tcx>,
    pub(in crate::reader::ownership::shadow) roots: Vec<RootPlan<'tcx>>,
    pub(in crate::reader::ownership::shadow) types: Vec<TypeNode<'tcx>>,
    pub(in crate::reader::ownership::shadow) declarations: Vec<DeclarationPlan>,
    pub(in crate::reader::ownership::shadow) frames: HashMap<LocalDefId, Frame<'tcx>>,
    type_ids: HashMap<(ty::Ty<'tcx>, LocalDefId, u8), TypeId>,
    declaration_ids: HashMap<LocalDefId, DeclarationId>,
    /// Explicit remaining obligations, never a completed-native flag.
    pub(in crate::reader::ownership::shadow) requirements: Vec<String>,
    remaining_work: Cell<usize>,
}

impl<'cx, 'tcx> LiveGraph<'cx, 'tcx> {
    pub(in crate::reader::ownership::shadow) fn collect(
        cx: &'cx Cx<'tcx>,
        roots: &[LocalDefId],
    ) -> Result<Self, String> {
        if roots.is_empty()
            || roots.len() > 65_536
            || roots.iter().copied().collect::<HashSet<_>>().len() != roots.len()
        {
            return Err(
                "a live shadow graph needs distinct actual native roots within its bound".into(),
            );
        }
        let mut types = Types {
            cx,
            nodes: Vec::new(),
            node_ids: HashMap::new(),
            declarations: Vec::new(),
            declaration_ids: HashMap::new(),
            frames: HashMap::new(),
            next_generic: 0,
            remaining: 262_144,
            requirements: Vec::new(),
        };
        let mut captured = Vec::new();
        let mut pending = roots.to_vec();
        let mut queued = roots.iter().copied().collect::<HashSet<_>>();
        let mut cursor = 0;
        while cursor < pending.len() {
            types.spend(0)?;
            let current_definition = pending[cursor];
            let definition = &current_definition;
            let source = SourceInventory::collect_with_work(cx, *definition, &mut types.remaining)?;
            types.frame(*definition)?;
            let mut call_types = HashMap::new();
            let mut call_positions = HashMap::new();
            let mut construction_types = HashMap::new();
            for (call_index, call) in source.calls.iter().enumerate() {
                call_positions.insert(call.expression.hir_id, call_index);
                types.spend(0)?;
                if cx.tcx.def_kind(call.target) == rustc_hir::def::DefKind::Fn {
                    let local = call
                        .target
                        .as_local()
                        .ok_or("a foreign direct call has no source body in the shadow closure")?;
                    if cx.tcx.def_kind(cx.tcx.local_parent(local)) != rustc_hir::def::DefKind::Mod {
                        return Err("a non-free native call needs its actual instance/declaration correspondence".into());
                    }
                    if queued.insert(local) {
                        if pending.len() >= 65_536 {
                            return Err(
                                "the complete source call closure exceeds its root bound".into()
                            );
                        }
                        pending.push(local);
                    }
                } else if matches!(
                    cx.tcx.def_kind(call.target),
                    rustc_hir::def::DefKind::Ctor(..)
                ) {
                    construction_types.insert(
                        call.expression.hir_id,
                        types.request(
                            source.typeck.expr_ty(call.expression),
                            *definition,
                            Position::ShadowStorage,
                            0,
                        )?,
                    );
                } else {
                    return Err(
                        "a source call target has no complete local body or constructor mapping"
                            .into(),
                    );
                }
                let mut arguments = Vec::new();
                for argument in call.arguments.iter() {
                    let ty = argument.as_type().ok_or("source call lifetime/const arguments require a complete target frame mapping")?;
                    arguments.push(types.request(ty, *definition, Position::ShadowStorage, 0)?);
                }
                if call_types
                    .insert(call.expression.hir_id, arguments)
                    .is_some()
                {
                    return Err("a native source call has duplicate closure entries".into());
                }
            }
            let mut parameters = Vec::new();
            for (parameter, slot) in &source.signature.parameters {
                parameters.push((
                    *parameter,
                    types.request(
                        slot.original,
                        *definition,
                        Position::Parameter(slot.mode),
                        0,
                    )?,
                ));
            }
            let result = types.request(
                source.signature.result.original,
                *definition,
                Position::Result(source.signature.result.mode),
                0,
            )?;
            let mut bindings = HashMap::new();
            for (pattern, slot) in &source.bindings {
                if bindings
                    .insert(
                        pattern.hir_id,
                        types.request(
                            slot.original,
                            *definition,
                            Position::Storage(slot.mode),
                            0,
                        )?,
                    )
                    .is_some()
                {
                    return Err("a source binding has duplicate graph slots".into());
                }
            }
            let mut expressions = Vec::new();
            for observed in source.checked.expressions.observations() {
                types.spend(0)?;
                if matches!(observed.expression.kind, hir::ExprKind::Struct(..)) {
                    let retained = types.request(
                        source.typeck.expr_ty(observed.expression),
                        *definition,
                        Position::ShadowStorage,
                        0,
                    )?;
                    if construction_types
                        .insert(observed.expression.hir_id, retained)
                        .is_some_and(|old| old != retained)
                    {
                        return Err("one native struct occurrence changed its retained type".into());
                    }
                }
                let context = observed.context;
                expressions.push(ExpressionPlan {
                    original: observed.expression,
                    context: ExpressionContext {
                        outer: context.outer,
                        expected: context.expected,
                        pure: context.pure,
                        proof_in_spec: context.proof_in_spec,
                        assert_by: context.assert_by,
                        block_ghost: context.block_ghost,
                        uses_ghost_blocks: context.uses_ghost_blocks,
                    },
                    result: observed.result,
                    native_type: types.request(
                        observed.native_type,
                        *definition,
                        Position::Value(observed.result),
                        0,
                    )?,
                    adjusted_type: types.request(
                        observed.adjusted_type,
                        *definition,
                        Position::Value(observed.result),
                        0,
                    )?,
                });
            }
            let mut condition_scopes = HashMap::new();
            for control in &source.controls {
                types.spend(0)?;
                match control {
                    Control::If { condition, .. } => {
                        if condition_scopes
                            .insert(condition.hir_id, *condition)
                            .is_some()
                        {
                            return Err("duplicate native condition/scope identity".into());
                        }
                        let _ = types.request(
                            source.typeck.expr_ty_adjusted(condition),
                            *definition,
                            Position::ControlBoolean,
                            0,
                        )?;
                    }
                    Control::Match {
                        scrutinee,
                        scrutinee_mode: Mode::Spec,
                        ..
                    } => {
                        if source.typeck.expr_ty_adjusted(scrutinee).is_bool() {
                            let _ = types.request(
                                source.typeck.expr_ty_adjusted(scrutinee),
                                *definition,
                                Position::ControlBoolean,
                                0,
                            )?;
                        } else {
                            types.requirements.push("a Spec match needs a complete inhabited variant-choice/control representation, not a unit scrutinee".into());
                        }
                    }
                    _ => {}
                }
            }
            let mut adjustment_ids = HashSet::new();
            for adjustment in &source.adjustments {
                types.spend(0)?;
                if !adjustment_ids.insert(adjustment.expression) {
                    return Err("duplicate native adjustment index".into());
                }
            }
            source.revalidate_with_work(cx, &mut types.remaining)?;
            captured.push(RootPlan {
                source,
                parameters,
                result,
                bindings,
                expressions,
                call_types,
                call_positions,
                condition_scopes,
                construction_types,
                adjustment_ids,
            });
            cursor += 1;
        }
        if types
            .nodes
            .iter()
            .any(|node| matches!(node.shape, Shape::Pending))
        {
            return Err("the native source type walk did not finish an issued node".into());
        }
        types.requirements.extend([
            "close the fresh native expression/control/availability correspondence against the complete source call closure".into(),
            "map and validate every actual fresh AST/HIR/call/scope/type/signature role".into(),
            "close genuine helper cohort, original/native option and region/predicate correspondence".into(),
            "execute one real whole-program native borrow transaction before source eligibility or AY".into(),
        ]);
        let graph = Self {
            cx,
            roots: captured,
            types: types.nodes,
            declarations: types.declarations,
            frames: types.frames,
            type_ids: types.node_ids,
            declaration_ids: types.declaration_ids,
            requirements: types.requirements,
            remaining_work: Cell::new(types.remaining),
        };
        graph.revalidate()?;
        Ok(graph)
    }

    pub(in crate::reader::ownership::shadow) fn type_for(
        &self,
        original: ty::Ty<'tcx>,
        owner: LocalDefId,
        position: Position,
    ) -> Result<TypeId, String> {
        self.revalidate()?;
        self.type_ids
            .get(&(original, owner, position.key()))
            .copied()
            .ok_or("this source type/owner/position was not included in the live graph".into())
    }

    pub(in crate::reader::ownership::shadow) fn revalidate(&self) -> Result<(), String> {
        let mut remaining = self.remaining_work.get();
        let result = self.revalidate_with_work(&mut remaining);
        // Keep consumed work even when a later join fails. An error must
        // not refill a live graph before a subsequent validation attempt.
        self.remaining_work.set(remaining);
        result
    }

    fn revalidate_with_work(&self, remaining: &mut usize) -> Result<(), String> {
        super::spend(remaining, 1)?;
        if self.cx.tcx.dcx().has_errors().is_some() {
            return Err("native errors revoked the live source graph".into());
        }
        for root in &self.roots {
            root.source.revalidate_with_work(self.cx, remaining)?;
        }
        for (owner, frame) in &self.frames {
            super::spend(remaining, 1)?;
            if super::super::super::super::function_identity_observer::body_is_quarantined(
                self.cx.tcx.sess,
                *owner,
            ) {
                return Err("a quarantined native owner revoked the live source frame".into());
            }
            let current = self.cx.tcx.generics_of(*owner);
            super::spend(remaining, current.own_params.len())?;
            super::spend(remaining, frame.predicates.len())?;
            if frame.owner != *owner
                || !std::ptr::eq(current, frame.original)
                || current.parent != frame.inherited_parent
                || current.own_params.len()
                    != frame.type_parameters.len() + frame.regions.len() + frame.constants.len()
                || current
                    .own_params
                    .iter()
                    .any(|parameter| !frame.parameter_ids.contains(&parameter.def_id))
                || self.cx.tcx.clauses_of(*owner).clauses != frame.predicates.as_slice()
            {
                return Err("the live source graph changed its actual native generic frame".into());
            }
        }
        for declaration in &self.declarations {
            super::spend(remaining, 1)?;
            let tcx = self.cx.tcx;
            let actual = tcx.adt_def(declaration.source);
            if (!actual.is_enum() && !actual.is_struct())
                || actual.is_enum() != declaration.is_enum
                || actual.variants().len() != declaration.variants.len()
            {
                return Err(
                    "the actual native declaration changed its struct/enum kind or variant layout"
                        .into(),
                );
            }
            let attributes = attrs::item_attrs_with_work(
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(declaration.source)),
                remaining,
            )?;
            if declaration.is_enum != actual.is_enum()
                || (!actual.is_enum() && !actual.is_struct())
                || actual.variants().len() != declaration.variants.len()
                || attributes.external
                || attributes.external_body
                || attributes.uninterp
                || !attributes.unsupported.is_empty()
            {
                return Err("the live source datatype kind/policy/inventory changed".into());
            }
            for (variant, planned) in actual.variants().iter().zip(&declaration.variants) {
                super::spend(remaining, 1)?;
                if variant.def_id != planned.source || variant.fields.len() != planned.fields.len()
                {
                    return Err(
                        "the live source datatype changed its original variant/field declarations"
                            .into(),
                    );
                }
                for (field, planned) in variant.fields.iter().zip(&planned.fields) {
                    super::spend(remaining, 1)?;
                    let local = field
                        .did
                        .as_local()
                        .ok_or("a source field became foreign")?;
                    if super::super::super::super::function_identity_observer::body_is_quarantined(
                        tcx.sess, local,
                    ) {
                        return Err("a quarantined native field revoked its source layout".into());
                    }
                    let mode = super::super::super::super::datatypes::field_mode_with_work(
                        tcx,
                        field,
                        tcx.def_span(field.did),
                        remaining,
                    )
                    .map_err(|refusal| refusal.detail)?;
                    let ty = self
                        .types
                        .get(planned.ty.0)
                        .ok_or("a source field lost its declared type node")?;
                    if field.did != planned.source
                        || mode != planned.mode
                        || ty.owner != declaration.source
                        || ty.position != Position::Field(mode)
                        || ty.original
                            != tcx
                                .type_of(field.did)
                                .instantiate_identity()
                                .skip_normalization()
                    {
                        return Err(
                            "a source field changed its exact native type/mode/declaration join"
                                .into(),
                        );
                    }
                }
            }
        }
        Ok(())
    }
}

struct Types<'cx, 'tcx> {
    cx: &'cx Cx<'tcx>,
    nodes: Vec<TypeNode<'tcx>>,
    node_ids: HashMap<(ty::Ty<'tcx>, LocalDefId, u8), TypeId>,
    declarations: Vec<DeclarationPlan>,
    declaration_ids: HashMap<LocalDefId, DeclarationId>,
    frames: HashMap<LocalDefId, Frame<'tcx>>,
    next_generic: u32,
    remaining: usize,
    requirements: Vec<String>,
}
impl<'tcx> Types<'_, 'tcx> {
    fn spend(&mut self, depth: usize) -> Result<(), String> {
        if self.remaining == 0 || depth >= 128 {
            return Err("the whole live source type graph exceeds its shared bound".into());
        }
        self.remaining -= 1;
        Ok(())
    }
    fn frame(&mut self, owner: LocalDefId) -> Result<(), String> {
        if self.frames.contains_key(&owner) {
            return Ok(());
        }
        let native = self.cx.tcx.generics_of(owner);
        let mut types = Vec::new();
        let mut regions = Vec::new();
        let mut constants = Vec::new();
        for parameter in &native.own_params {
            self.spend(0)?;
            match parameter.kind {
                ty::GenericParamDefKind::Type { .. } => {
                    let target = GenericId(self.next_generic);
                    self.next_generic = self
                        .next_generic
                        .checked_add(1)
                        .ok_or("native generic allocation is exhausted")?;
                    types.push((parameter.def_id, target));
                }
                ty::GenericParamDefKind::Lifetime => regions.push(parameter.def_id),
                ty::GenericParamDefKind::Const { .. } => constants.push(parameter.def_id),
            }
        }
        if native.parent.is_some() {
            self.requirements.push("a source generic frame has an inherited native parent which still needs a complete target join".into());
        }
        if !regions.is_empty() || !constants.is_empty() {
            self.requirements.push(
                "native region/const binders require their full independent-compiler mapping"
                    .into(),
            );
        }
        let native_predicates = self.cx.tcx.clauses_of(owner).clauses;
        for _ in native_predicates {
            self.spend(0)?;
        }
        let predicates = native_predicates.to_vec();
        if !predicates.is_empty() {
            self.requirements.push("source generic predicates are retained data and still need their actual target predicate join".into());
        }
        let type_targets = types.iter().copied().collect();
        let parameter_ids = native
            .own_params
            .iter()
            .map(|parameter| parameter.def_id)
            .collect();
        self.frames.insert(
            owner,
            Frame {
                owner,
                original: native,
                type_parameters: types,
                regions,
                constants,
                predicates,
                inherited_parent: native.parent,
                parameter_ids,
                type_targets,
            },
        );
        Ok(())
    }

    fn request(
        &mut self,
        original: ty::Ty<'tcx>,
        owner: LocalDefId,
        position: Position,
        depth: usize,
    ) -> Result<TypeId, String> {
        self.spend(depth)?;
        let key = (original, owner, position.key());
        if let Some(id) = self.node_ids.get(&key) {
            return Ok(*id);
        }
        let id = TypeId(self.nodes.len());
        self.node_ids.insert(key, id);
        self.nodes.push(TypeNode {
            original,
            owner,
            position,
            shape: Shape::Pending,
        });
        let shape = if position.erases_storage() {
            // This is a target declaration requirement, not changing an
            // existing native Ty or fn_sig/typeck query. The real fresh
            // compiler must materialize and rejoin the unit signature/field.
            Shape::ErasedUnit
        } else if position == Position::ControlBoolean {
            if original.is_bool() {
                Shape::Bool
            } else {
                Shape::Unmaterialized("a control proxy needs the actual native bool type".into())
            }
        } else {
            match original.kind() {
                ty::Bool => Shape::Bool,
                ty::Never if position == Position::ShadowStorage => Shape::Unmaterialized("known native never storage cannot be a shadow initializer".into()),
                ty::Never => Shape::Never,
                ty::Int(value) => Shape::Signed(match value { ty::IntTy::I8 => Signed::I8, ty::IntTy::I16 => Signed::I16, ty::IntTy::I32 => Signed::I32, ty::IntTy::I64 => Signed::I64, ty::IntTy::I128 => Signed::I128, ty::IntTy::Isize => Signed::Isize }),
                ty::Uint(value) => Shape::Unsigned(match value { ty::UintTy::U8 => Unsigned::U8, ty::UintTy::U16 => Unsigned::U16, ty::UintTy::U32 => Unsigned::U32, ty::UintTy::U64 => Unsigned::U64, ty::UintTy::U128 => Unsigned::U128, ty::UintTy::Usize => Unsigned::Usize }),
                ty::Tuple(fields) if fields.is_empty() => Shape::Unit,
                ty::Tuple(fields) => { let mut result = Vec::new(); for field in fields.iter() { result.push(self.request(field, owner, position, depth + 1)?); } Shape::Tuple(result) }
                ty::Param(parameter) => {
                    self.frame(owner)?;
                    let generics = self.cx.tcx.generics_of(owner);
                    if parameter.index as usize >= generics.count() { return Err("a current native type parameter is outside its actual source frame".into()); }
                    let source = generics.param_at(parameter.index as usize, self.cx.tcx).def_id;
                    if let Some(target) = self.frames[&owner].type_targets.get(&source).copied() { Shape::Parameter { source, target } }
                    else { Shape::Unmaterialized("a parent-owned native type parameter needs an explicit target frame".into()) }
                }
                ty::Ref(region, target, mutability) => {
                    let target = self.request(*target, owner, position, depth + 1)?;
                    self.requirements.push("a native reference retains its original region; availability/alias/owned resolution and full target region join remain required".into());
                    Shape::Reference { region: *region, mutable: mutability.is_mut(), target }
                }
                ty::Adt(definition, arguments) => {
                    if let Some(local) = definition.did().as_local().filter(|_| self.cx.adt_id(definition.did()).is_some() && !self.cx.source_opaque_nominal(definition.did())) {
                        let declaration = self.declaration(local, depth + 1)?;
                        let mut types = Vec::new(); let mut unsupported = false;
                        for argument in arguments.iter() { if let Some(ty) = argument.as_type() { types.push(self.request(ty, owner, position, depth + 1)?); } else { unsupported = true; } }
                        if unsupported { Shape::Unmaterialized("a native datatype's region/const arguments need their full target mapping".into()) }
                        else { Shape::Adt { declaration, arguments: types } }
                    } else { Shape::Unmaterialized("foreign, opaque or unrepresented native datatype fields have no source-layout authority here".into()) }
                }
                ty::Alias(..) => Shape::Unmaterialized("a native alias/projection needs normalization with its full original region/frame relation".into()),
                _ => Shape::Unmaterialized("this native type needs a first-class target declaration/type mapping".into()),
            }
        };
        if let Shape::Unmaterialized(problem) = &shape {
            self.requirements.push(problem.clone());
        }
        self.nodes[id.0].shape = shape;
        Ok(id)
    }

    fn declaration(&mut self, owner: LocalDefId, depth: usize) -> Result<DeclarationId, String> {
        self.spend(depth)?;
        if let Some(id) = self.declaration_ids.get(&owner) {
            return Ok(*id);
        }
        if self.declarations.len() >= 65_536 {
            return Err("the native declaration graph exceeds its bound".into());
        }
        let tcx = self.cx.tcx;
        if tcx.dcx().has_errors().is_some()
            || super::super::super::super::function_identity_observer::body_is_quarantined(
                tcx.sess, owner,
            )
        {
            return Err(
                "native diagnostics or quarantine reject source declaration capture".into(),
            );
        }
        let adt = tcx.adt_def(owner);
        let attributes = attrs::item_attrs_with_work(
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
            &mut self.remaining,
        )?;
        if (!adt.is_enum() && !adt.is_struct())
            || attributes.external
            || attributes.external_body
            || attributes.uninterp
            || !attributes.unsupported.is_empty()
        {
            return Err(
                "a shadow declaration requires its actual ordinary local represented datatype"
                    .into(),
            );
        }
        self.frame(owner)?;
        let id = DeclarationId(self.declarations.len());
        self.declaration_ids.insert(owner, id);
        self.declarations.push(DeclarationPlan {
            source: owner,
            is_enum: adt.is_enum(),
            variants: Vec::new(),
        });
        let mut variants = Vec::new();
        for variant in adt.variants().iter() {
            self.spend(depth)?;
            let mut fields = Vec::new();
            for field in &variant.fields {
                self.spend(depth)?;
                let mode = match super::super::super::super::datatypes::field_mode_with_work(
                    tcx,
                    field,
                    tcx.def_span(field.did),
                    &mut self.remaining,
                ) {
                    Ok(mode) => mode,
                    Err(error) => {
                        attrs::charge_format(
                            format_args!("native field-mode capture failed: {error:?}"),
                            &mut self.remaining,
                        )?;
                        return Err(format!("native field-mode capture failed: {error:?}"));
                    }
                };
                // Raw declared type is retained as source data only. An alias
                // becomes Unmaterialized above; no skip-normalized fact is
                // supplied to the native compiler or ownership consumer.
                let original = tcx
                    .type_of(field.did)
                    .instantiate_identity()
                    .skip_normalization();
                let ty = self.request(original, owner, Position::Field(mode), depth + 1)?;
                fields.push(FieldPlan {
                    source: field.did,
                    mode,
                    ty,
                });
            }
            variants.push(VariantPlan {
                source: variant.def_id,
                fields,
            });
        }
        self.declarations[id.0].variants = variants;
        if tcx.dcx().has_errors().is_some()
            || super::super::super::super::function_identity_observer::body_is_quarantined(
                tcx.sess, owner,
            )
        {
            return Err("native diagnostics revoked source declaration capture".into());
        }
        Ok(id)
    }
}
