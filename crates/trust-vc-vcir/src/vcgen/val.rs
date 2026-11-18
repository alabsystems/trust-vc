//! Values as trees of scalar terms, and the crate-wide lookup context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Scalar leaves use `Bool`, `Int` or a declared nominal carrier. A scalar
//! is one term, and a transparent struct, a tuple or `()`
//! is a node holding one value per field (`()` has none). A reference is its
//! referent: shared references are transparent to verification, and a
//! `&mut` parameter's current and entry values are tracked like any other
//! local's. Finite acyclic enums use typed boxed sum values. Recursive
//! sums and `char` values remain outside this representation.

use std::collections::{BTreeMap, HashMap};

use crate::ids::{AdtId, FnId, LocalId, SpanId};
use crate::item::{AdtDecl, AdtKind, Clause, DefOrder, FnDecl, RecGroup, VcCrate};
use crate::ty::{IntRange, Ty};

use super::query::VcRefusal;
use super::term::{Sort, Term};
use super::type_encoding::{
    ProductFamily, RecipeAdt, TypeArgument, TypeEnv, TypeRecipe, Vocabulary,
};

mod mut_refs;
mod product_values;
mod sum_values;
pub(crate) use product_values::{FormalPosition, FormalValue};

/// The type of one scalar leaf.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum LeafTy {
    Bool,
    Int(IntRange),
    /// An abstract nominal value. The index preserves the full declaration
    /// and type arguments in the crate context's registry.
    Nominal(u32),
    /// A boxed value with a type recipe interpreted in its binder scope.
    Poly(u32),
}

impl LeafTy {
    pub(crate) const fn sort(self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Int(_) => Sort::Int,
            Self::Nominal(index) => Sort::Nominal(index),
            Self::Poly(_) => Sort::Poly,
        }
    }

    /// Smallest and largest value, when bounded.
    pub(crate) fn bounds(self) -> (Option<i128>, Option<u128>) {
        match self {
            Self::Bool | Self::Nominal(_) | Self::Poly(_) => (None, None),
            Self::Int(range) => range_bounds(range),
        }
    }

    /// The fact that `term` is a value of this type (`true` when every
    /// value of the sort is).
    pub(crate) fn fact(self, term: &Term) -> Term {
        let (lo, hi) = self.bounds();
        term.within_type_bounds(lo, hi)
    }
}

/// Bounds of a fixed mathematical carrier. Callers resolve pointer-sized
/// ranges with [`concrete_range`] in their complete architecture context.
pub(crate) fn range_bounds(range: IntRange) -> (Option<i128>, Option<u128>) {
    let lo = range.min(64);
    let hi = range.max(64);
    (lo, hi)
}

/// Resolve only the mathematical carrier bounds. Source `Ty` and recipes
/// retain `usize`/`isize`, so generic/nominal identities never alias u32/u64.
pub(crate) fn concrete_range(range: IntRange, width: u32) -> IntRange {
    match range {
        IntRange::USize => IntRange::U(width),
        IntRange::ISize => IntRange::I(width),
        other => other,
    }
}

/// Is `range` one the complete-context generator handles? `char` has gaps.
pub(crate) fn supported_range(range: IntRange) -> Result<(), (&'static str, String)> {
    match range {
        IntRange::Int | IntRange::Nat => Ok(()),
        IntRange::U(bits) | IntRange::I(bits) if bits <= 128 && range.is_valid() => Ok(()),
        IntRange::U(_) | IntRange::I(_) => Err(("int128", format!("the integer type {range:?}"))),
        IntRange::USize | IntRange::ISize => Ok(()),
        IntRange::Char => Err(("char", "char values".to_string())),
    }
}

/// The layout of a value: scalar leaves in a tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Shape {
    Leaf(LeafTy),
    Node(Vec<Shape>),
}

impl Shape {
    pub(crate) fn has_poly(&self) -> bool {
        match self {
            Self::Leaf(leaf) => matches!(leaf, LeafTy::Poly(_)),
            Self::Node(children) => children.iter().any(Self::has_poly),
        }
    }

    /// Every leaf type, in order.
    pub(crate) fn leaves(&self, out: &mut Vec<LeafTy>) {
        match self {
            Self::Leaf(leaf) => out.push(*leaf),
            Self::Node(children) => {
                for child in children {
                    child.leaves(out);
                }
            }
        }
    }
}

/// A value: one term per scalar leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Val {
    Leaf(Term),
    Node(Vec<Val>),
}

impl Val {
    /// Exact product structure and scalar sorts, without adding type facts.
    pub(crate) fn matches(&self, shape: &Shape) -> bool {
        match (self, shape) {
            (Self::Leaf(term), Shape::Leaf(leaf)) => term.sort() == leaf.sort(),
            (Self::Node(values), Shape::Node(shapes)) => {
                values.len() == shapes.len()
                    && values
                        .iter()
                        .zip(shapes)
                        .all(|(value, shape)| value.matches(shape))
            }
            _ => false,
        }
    }

    /// The unit value.
    pub(crate) const fn unit() -> Self {
        Self::Node(Vec::new())
    }

    /// The term of a scalar value.
    pub(crate) fn into_leaf(self) -> Option<Term> {
        match self {
            Self::Leaf(term) => Some(term),
            Self::Node(_) => None,
        }
    }

    /// Every leaf term, in order.
    pub(crate) fn leaves(&self, out: &mut Vec<Term>) {
        match self {
            Self::Leaf(term) => out.push(term.clone()),
            Self::Node(children) => {
                for child in children {
                    child.leaves(out);
                }
            }
        }
    }

    /// Child `index` of a node.
    pub(crate) fn child(&self, index: u32) -> Option<&Self> {
        match self {
            Self::Node(children) => children.get(index as usize),
            Self::Leaf(_) => None,
        }
    }

    /// Replace child `index` of a node.
    pub(crate) fn with_child(&self, index: u32, value: Self) -> Option<Self> {
        match self {
            Self::Node(children) => {
                let mut children = children.clone();
                *children.get_mut(index as usize)? = value;
                Some(Self::Node(children))
            }
            Self::Leaf(_) => None,
        }
    }

    /// Leafwise equality of two values of one shape.
    pub(crate) fn equal(&self, other: &Self) -> Option<Term> {
        match (self, other) {
            (Self::Leaf(a), Self::Leaf(b)) => Some(Term::eq(a.clone(), b.clone())),
            (Self::Node(a), Self::Node(b)) if a.len() == b.len() => {
                let mut parts = Vec::new();
                for (x, y) in a.iter().zip(b) {
                    parts.push(x.equal(y)?);
                }
                Some(Term::and(parts))
            }
            _ => None,
        }
    }

    /// Leafwise `if cond then self else other`.
    pub(crate) fn select(cond: &Term, a: &Self, b: &Self) -> Option<Self> {
        match (a, b) {
            (Self::Leaf(x), Self::Leaf(y)) => {
                Some(Self::Leaf(Term::ite(cond.clone(), x.clone(), y.clone())))
            }
            (Self::Node(xs), Self::Node(ys)) if xs.len() == ys.len() => {
                let mut children = Vec::new();
                for (x, y) in xs.iter().zip(ys) {
                    children.push(Self::select(cond, x, y)?);
                }
                Some(Self::Node(children))
            }
            _ => None,
        }
    }
}

/// Lookup tables shared by everything the generator does for one crate.
#[derive(Default)]
struct NominalTypes {
    types: Vec<Ty>,
    indices: HashMap<Ty, u32>,
}

/// The checked source's diagnostic clauses retain its own parameter indices.
/// No body or header is installed onto a bodyless imported declaration.
pub(crate) struct SpecRecommendations {
    pub(crate) params: Vec<LocalId>,
    pub(crate) clauses: Vec<Clause>,
}

/// Lookup tables shared by everything the generator does for one crate.
pub(crate) struct Ctx<'a> {
    pub(crate) bitvector_policy: super::BitvectorPolicy,
    pub(crate) source: &'a VcCrate,
    pub(super) generation_identity: std::rc::Rc<()>,
    pub(crate) pointer_width: u32,
    pub(crate) architecture: crate::bitvector::Architecture,
    pub(crate) fns: HashMap<FnId, &'a FnDecl>,
    checked_spec_recommendations: HashMap<FnId, SpecRecommendations>,
    checked_inline_forwarders: HashMap<FnId, FnDecl>,
    validated_instances: std::collections::HashSet<FnId>,
    pub(crate) adts: HashMap<AdtId, &'a AdtDecl>,
    projections: HashMap<crate::ProjectionId, &'a crate::ProjectionDecl>,
    projection_definitions: Option<crate::projection_types::Definitions<'a>>,
    projection_rules_ready: std::cell::Cell<bool>,
    def_order: BTreeMap<FnId, BTreeMap<FnId, DefOrder>>,
    /// The group of recursive functions of each member.
    groups: HashMap<FnId, &'a RecGroup>,
    /// The crate's quantifiers and choices, registered as they are
    /// translated.
    pub(crate) quants: std::cell::RefCell<super::quant::Registry>,
    /// Actual complete VcIR types, never display names or a truncated hash.
    nominal_types: std::cell::RefCell<NominalTypes>,
    types: std::cell::RefCell<Vocabulary>,
}

impl<'a> Ctx<'a> {
    #[cfg(test)]
    pub(crate) fn new(krate: &'a VcCrate) -> Self {
        Self::for_width(krate, krate.pointer_width)
    }

    pub(crate) fn for_width(krate: &'a VcCrate, pointer_width: u32) -> Self {
        let fns: HashMap<_, _> = krate.fns.iter().map(|decl| (decl.id, decl)).collect();
        let projection_definitions = crate::projection_types::Definitions::checked(krate, &mut crate::copy_context::WF_WORK);
        let validated_instances = crate::instance_semantics::validated_origins_with_definitions(&fns, projection_definitions.as_ref());
        let mut groups = HashMap::new();
        for group in &krate.rec_groups {
            for (id, _) in &group.members {
                groups.insert(*id, group);
            }
        }
        let origins: HashMap<_, _> = krate
            .fns
            .iter()
            .filter_map(|decl| {
                decl.attrs
                    .instance
                    .as_ref()
                    .map(|origin| (decl.id, origin.declaration))
            })
            .collect();
        let mut def_order = krate.def_order.clone();
        for order in def_order.values_mut() {
            for (id, why) in order.clone() {
                if let Some(original) = origins.get(&id) {
                    let merged = match (order.get(original), why) {
                        (Some(DefOrder::Later), _) | (_, DefOrder::Later) => DefOrder::Later,
                        _ => DefOrder::Unknown,
                    };
                    order.insert(*original, merged);
                }
            }
        }
        Self {
            bitvector_policy: super::BitvectorPolicy::default(),
            source: krate,
            generation_identity: std::rc::Rc::new(()),
            pointer_width,
            architecture: krate.architecture,
            fns,
            checked_spec_recommendations: HashMap::new(),
            checked_inline_forwarders: HashMap::new(),
            validated_instances,
            adts: krate.adts.iter().map(|adt| (adt.id, adt)).collect(),
            projections: krate.projections.iter().map(|decl| (decl.id, decl)).collect(),
            projection_definitions,
            projection_rules_ready: std::cell::Cell::new(false),
            def_order,
            groups,
            quants: std::cell::RefCell::default(),
            nominal_types: std::cell::RefCell::default(),
            types: std::cell::RefCell::default(),
        }
    }

    /// Retain separate checked source environments after exact signature
    /// validation. The ordinary declaration table remains bodyless; only the
    /// bounded inline path consumes a finite forwarder's actual source body.
    pub(crate) fn for_width_with_checked_spec(
        krate: &'a VcCrate,
        pointer_width: u32,
        definitions: &crate::CheckedSpecDefinitions,
    ) -> Self {
        let mut ctx = Self::for_width(krate, pointer_width);
        ctx.checked_inline_forwarders = definitions
            .definitions()
            .filter(|definition| definition.attrs.inline)
            .map(|definition| (definition.id, definition.clone()))
            .collect();
        ctx.checked_spec_recommendations = definitions
            .recommendation_declarations()
            .map(|definition| {
                (
                    definition.id,
                    SpecRecommendations {
                        params: definition.params.clone(),
                        clauses: definition.recommends.clone(),
                    },
                )
            })
            .collect();
        ctx
    }

    pub(crate) fn checked_spec_recommendations(&self, owner: FnId) -> Option<&SpecRecommendations> {
        self.checked_spec_recommendations.get(&owner)
    }

    pub(crate) fn checked_inline_forwarder(&self, owner: FnId) -> Option<&FnDecl> {
        self.checked_inline_forwarders.get(&owner)
    }

    /// The group of recursive functions `id` belongs to.
    pub(crate) fn group(&self, id: FnId) -> Option<&'a RecGroup> {
        self.groups.get(&id).copied()
    }

    /// Are `a` and `b` members of one group (a call from one to the other
    /// is a recursive call)?
    pub(crate) fn same_group(&self, a: FnId, b: FnId) -> bool {
        self.group(a).is_some_and(|group| group.contains(b))
    }

    /// The length of the shortest cycle from `id` back to itself, for a
    /// member of a group.
    pub(crate) fn cycle_len(&self, id: FnId) -> Option<u32> {
        self.group(id)?
            .members
            .iter()
            .find(|(member, _)| *member == id)
            .map(|(_, cycle)| *cycle)
    }

    /// The spec functions whose definitions `function` may not see
    /// ([`VcCrate::def_order`]).
    pub(crate) fn def_order(&self, function: FnId) -> Option<&BTreeMap<FnId, DefOrder>> {
        self.def_order.get(&function)
    }

    /// Read-only association already established by the existing Spec body
    /// matcher. Executable contract correspondence never joins this set.
    pub(super) fn checked_spec_original(&self, callee: FnId) -> Option<&'a FnDecl> {
        if !self.validated_instances.contains(&callee) {
            return None;
        }
        let origin = self.fns.get(&callee)?.attrs.instance.as_ref()?;
        self.fns.get(&origin.declaration).copied()
    }

    pub(crate) fn call_origin(
        &self,
        callee: FnId,
        type_args: &[Ty],
        span: SpanId,
    ) -> Result<(FnId, Vec<Ty>), VcRefusal> {
        let declaration = self
            .fns
            .get(&callee)
            .ok_or_else(|| refusal("generic-instance", "an unknown call declaration", span))?;
        let Some(origin) = &declaration.attrs.instance else {
            return Ok((callee, type_args.to_vec()));
        };
        let original = self
            .fns
            .get(&origin.declaration)
            .ok_or_else(|| refusal("generic-instance", "a missing original declaration", span))?;
        if declaration.role != crate::FnRole::Instance
            || !type_args.is_empty()
            || original.role == crate::FnRole::Instance
            || original.attrs.instance.is_some()
            || original.role == crate::FnRole::Imported
            || origin.type_args.len() != original.type_params.len()
        {
            return Err(refusal(
                "generic-instance",
                "an unsupported or malformed native instance bridge",
                span,
            ));
        }
        if original.role == crate::FnRole::TraitDecl || original.attrs.is_trait_method_impl {
            return Ok((callee, Vec::new()));
        }
        if !self.validated_instances.contains(&callee) {
            return Ok((callee, Vec::new()));
        }
        Ok((origin.declaration, origin.type_args.clone()))
    }

    /// The layout of `ty`, or the reason it has none.
    pub(crate) fn shape(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
    ) -> Result<Shape, VcRefusal> {
        self.shape_inner(ty, owner, span, 0, None)
    }

    pub(crate) fn shape_with_work(&self, ty: &Ty, owner: Option<FnId>, span: SpanId, work: &std::cell::Cell<usize>) -> Result<Shape, VcRefusal> {
        if self.source.projections.is_empty() { return self.shape(ty, owner, span); }
        self.ensure_projection_rules(work, span)?;
        let ty = self.normalize_type(ty, work, span)?;
        self.shape_inner(&ty, owner, span, 0, Some(work))
    }

    fn type_recipe(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
    ) -> Result<TypeRecipe, VcRefusal> {
        TypeRecipe::registered(
            ty, owner, &|id| self.recipe_adt(id), &|id| self.recipe_projection(id),
        )
            .ok_or_else(|| refusal("generic-type", "an unsupported type-argument recipe", span))
    }

    fn recipe_adt(&self, id: crate::AdtId) -> Option<RecipeAdt> {
        let adt = self.adts.get(&id)?;
        match adt.kind {
            AdtKind::Opaque if adt.variants.is_empty() => {
                Some(RecipeAdt::Opaque(adt.type_params.len()))
            }
            AdtKind::Struct if adt.variants.len() == 1 => {
                Some(RecipeAdt::Struct(adt.type_params.len()))
            }
            AdtKind::Enum if !adt.variants.is_empty() => {
                Some(RecipeAdt::Enum(adt.type_params.len()))
            }
            _ => None,
        }
    }

    pub(in crate::vcgen) fn recipe_projection(&self, id: crate::ProjectionId) -> Option<usize> {
        let declaration = self.projections.get(&id)?;
        (declaration.arity != 0).then_some(declaration.arity)
    }

    pub(crate) fn type_argument(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        span: SpanId,
    ) -> Result<TypeArgument, VcRefusal> {
        let recipe = self.type_recipe(ty, env.owner(), span)?;
        self.types
            .borrow_mut()
            .argument(&recipe, env)
            .ok_or_else(|| {
                refusal(
                    "generic-type",
                    "a type argument outside its binder scope",
                    span,
                )
            })
    }

    pub(crate) fn type_argument_with_work(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        span: SpanId,
        work: &std::cell::Cell<usize>,
    ) -> Result<TypeArgument, VcRefusal> {
        let work = env.projection_work().map_or(work, |original| original.as_ref());
        self.ensure_projection_rules(work, span)?;
        let mut recipe = self.type_recipe(ty, env.owner(), span)?;
        if recipe.has_projection() {
            let normalized = self.normalize_type(ty, work, span)?;
            recipe = self.type_recipe(&normalized, env.owner(), span)?;
        }
        let argument = if self.source.projections.is_empty() {
            self.types.borrow_mut().argument_with_work(&recipe, env, work, span)?
        } else {
            self.types.borrow_mut().argument_with_allocation_work(&recipe, env, work, span)?
        }
            .ok_or_else(|| refusal(
                "generic-type", "a type argument outside its binder scope or constructor declaration", span,
            ))?;
        self.canonical_argument(argument, work, span)
    }

    fn ensure_projection_rules(&self, work: &std::cell::Cell<usize>, span: SpanId) -> Result<(), VcRefusal> {
        if self.projection_rules_ready.get() { return Ok(()); }
        if self.projection_definitions.is_none() { return Err(refusal("projection-definition", "invalid associated implementation semantics", span)); }
        for declaration in &self.source.projections {
            super::inline_work::items(work, 1, span)?;
            self.types.borrow_mut().register_projection_declaration(declaration.id, declaration.arity)
                .ok_or_else(|| refusal("projection-definition", "invalid associated declaration arity", span))?;
        }
        for implementation in &self.source.projection_impls {
            let env = TypeEnv::default();
            let arguments = implementation.arguments.iter().map(|ty| {
                super::aux_work::type_recipe(work, ty, span)?;
                let recipe = self.type_recipe(ty, None, span)?;
                self.types.borrow_mut().argument_with_allocation_work(&recipe, &env, work, span)?.ok_or_else(|| refusal("projection-definition", "an implementation argument is not a canonical closed type", span))
            }).collect::<Result<Vec<_>, _>>()?;
            for value in &implementation.values {
                super::aux_work::type_recipe(work, &value.ty, span)?;
                let recipe = self.type_recipe(&value.ty, None, span)?;
                let result = self.types.borrow_mut().argument_with_allocation_work(&recipe, &env, work, span)?.ok_or_else(|| refusal("projection-definition", "an associated member has no canonical closed value", span))?;
                self.types.borrow_mut().register_projection_definition(value.declaration, &arguments, &result, work, span)?;
            }
        }
        self.projection_rules_ready.set(true);
        Ok(())
    }

    pub(crate) fn canonical_type_terms(&self, term: Term, budget: &mut usize) -> Option<Term> {
        self.types.borrow().canonical_type_terms(term, budget)
    }

    fn canonical_argument(&self, argument: TypeArgument, work: &std::cell::Cell<usize>, span: SpanId) -> Result<TypeArgument, VcRefusal> {
        let mut remaining = work.get();
        let result = self.types.borrow().canonical_argument(argument, &mut remaining);
        work.set(remaining);
        result.ok_or_else(|| refusal("projection-definition", "type argument normalization exhausted its caller work", span))
    }

    pub(crate) fn normalize_type(&self, ty: &Ty, work: &std::cell::Cell<usize>, span: SpanId) -> Result<Ty, VcRefusal> {
        let definitions = self.projection_definitions.as_ref().ok_or_else(||
            refusal("projection-definition", "the program has invalid associated implementations", span))?;
        let mut remaining = work.get();
        let result = definitions.normalize(ty, &mut remaining);
        work.set(remaining);
        result.ok_or_else(|| refusal("projection-definition", "associated type normalization exhausted its caller work or declaration", span))
    }

    pub(crate) fn substitute_type(&self, ty: &Ty, arguments: &[Ty], work: &std::cell::Cell<usize>, span: SpanId) -> Result<Ty, VcRefusal> {
        // Programs without associated constructors retain their existing
        // substitution path. New semantic copies borrow the caller's ledger.
        if self.source.projections.is_empty() { return Ok(ty.subst(arguments)); }
        let definitions = self.projection_definitions.as_ref().ok_or_else(||
            refusal("projection-definition", "the program has invalid associated implementations", span))?;
        let mut remaining = work.get();
        let result = definitions.substitute(ty, arguments, &mut remaining);
        work.set(remaining);
        result.ok_or_else(|| refusal("projection-definition", "associated type substitution exhausted its caller work or declaration", span))
    }

    pub(crate) fn type_environment(
        &self,
        owner: FnId,
        arguments: Vec<TypeArgument>,
        work: &std::rc::Rc<std::cell::Cell<usize>>,
    ) -> TypeEnv {
        let mut environment = self.types.borrow().environment(owner, arguments, work);
        // Closed reduction can remove the constructor spelling while leaving
        // a large type term. Its forwarded copies still use this exact cell.
        if !self.source.projections.is_empty() { environment.retain_work(work); }
        environment
    }

    pub(crate) fn poly_shape(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
    ) -> Result<Shape, VcRefusal> {
        self.poly_shape_inner(ty, owner, span, &mut 64, None)
    }

    pub(crate) fn poly_shape_with_work(&self, ty: &Ty, owner: Option<FnId>, span: SpanId, work: &std::cell::Cell<usize>) -> Result<Shape, VcRefusal> {
        if self.source.projections.is_empty() { return self.poly_shape(ty, owner, span); }
        self.ensure_projection_rules(work, span)?;
        let ty = self.normalize_type(ty, work, span)?;
        self.poly_shape_inner(&ty, owner, span, &mut 64, Some(work))
    }

    fn field_type(&self, ty: &Ty, args: &[Ty], work: Option<&std::cell::Cell<usize>>, span: SpanId) -> Result<Ty, VcRefusal> {
        match work {
            Some(work) => self.substitute_type(ty, args, work, span),
            None if ty.has_projection() || args.iter().any(Ty::has_projection) =>
                Err(refusal("projection-layout", "a projected field layout has no original caller work", span)),
            None => Ok(ty.subst(args)),
        }
    }

    fn poly_shape_inner(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
        left: &mut usize,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Shape, VcRefusal> {
        *left = left.checked_sub(1).ok_or_else(|| {
            refusal(
                "generic-box",
                "a boxed layout exceeding its type budget",
                span,
            )
        })?;
        if let Ty::Adt(id, _) = ty {
            if self
                .adts
                .get(id)
                .is_some_and(|adt| adt.kind == AdtKind::Enum)
            {
                self.register_enum_with_work(*id, span, work)?;
            }
        }
        let children = match ty {
            Ty::Unit => Some(Vec::new()),
            Ty::Tuple(types) => {
                if types.len() > *left {
                    return Err(refusal(
                        "generic-box",
                        "a boxed layout exceeding its type budget",
                        span,
                    ));
                }
                Some(match work {
                    Some(work) => types.iter().map(|ty| self.normalize_type(ty, work, span)).collect::<Result<Vec<_>, _>>()?,
                    None => types.clone(),
                })
            }
            Ty::Adt(id, args)
                if self
                    .adts
                    .get(id)
                    .is_some_and(|adt| adt.kind == AdtKind::Struct) =>
            {
                let adt = self.adts[id];
                let variant = adt
                    .variants
                    .first()
                    .ok_or_else(|| refusal("generic-box", "a struct without fields", span))?;
                if variant.fields.len() > *left {
                    return Err(refusal(
                        "generic-box",
                        "a boxed layout exceeding its type budget",
                        span,
                    ));
                }
                Some(
                    variant
                        .fields
                        .iter()
                        .map(|field| self.field_type(&field.ty, args, work, span))
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Ty::Ref {
                mutable: false,
                inner,
            } if matches!(inner.as_ref(), Ty::Tuple(_) | Ty::Unit)
                || matches!(inner.as_ref(), Ty::Adt(id, _) if self.adts.get(id).is_some_and(|adt| adt.kind == AdtKind::Struct)) =>
            {
                return self.poly_shape_inner(inner, owner, span, left, work);
            }
            _ => None,
        };
        if let Some(children) = children {
            if children.len() > *left {
                return Err(refusal(
                    "generic-box",
                    "a boxed layout exceeding its type budget",
                    span,
                ));
            }
            return children
                .iter()
                .map(|ty| self.poly_shape_inner(ty, owner, span, left, work))
                .collect::<Result<Vec<_>, _>>()
                .map(Shape::Node);
        }
        let recipe = self.type_recipe(ty, owner, span)?;
        let index = self
            .types
            .borrow_mut()
            .intern(recipe)
            .ok_or_else(|| refusal("generic-type", "too many boxed type recipes", span))?;
        Ok(Shape::Leaf(LeafTy::Poly(index)))
    }

    pub(crate) fn type_fact(
        &self,
        leaf: LeafTy,
        env: &TypeEnv,
        term: &Term,
        span: SpanId,
    ) -> Result<Term, VcRefusal> {
        self.type_fact_inner(leaf, env, term, span, None)
    }

    pub(crate) fn type_fact_with_work(
        &self, leaf: LeafTy, env: &TypeEnv, term: &Term, span: SpanId,
        work: &std::cell::Cell<usize>,
    ) -> Result<Term, VcRefusal> {
        self.type_fact_inner(leaf, env, term, span, Some(work))
    }

    fn type_fact_inner(
        &self, leaf: LeafTy, env: &TypeEnv, term: &Term, span: SpanId,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Term, VcRefusal> {
        if let Some(work) = work { self.ensure_projection_rules(work, span)?; }
        let LeafTy::Poly(index) = leaf else {
            return Ok(leaf.fact(term));
        };
        let mut types = self.types.borrow_mut();
        let recipe = types
            .recipe(index)
            .cloned()
            .ok_or_else(|| refusal("generic-type", "an unknown boxed type recipe", span))?;
        let argument = match work {
            Some(work) => types.argument_with_work(&recipe, env, work, span)?,
            None => types.argument(&recipe, env),
        }.ok_or_else(|| {
            refusal(
                "generic-type",
                "a boxed value outside its binder scope",
                span,
            )
        })?;
        if types.requires_projection_work(&recipe, env) || env.projection_work().is_some() {
            let work = env.projection_work().map(|work| work.as_ref()).or(work)
                .ok_or_else(|| refusal("generic-type", "a projected type fact has no caller work", span))?;
            super::inline_work::term(work, term, 1, span)?;
            super::inline_work::term(work, argument.identity(), 1, span)?;
        }
        types
            .membership(term.clone(), argument.identity().clone())
            .ok_or_else(|| {
                refusal(
                    "generic-type",
                    "a boxed type fact with incompatible sorts",
                    span,
                )
            })
    }

    pub(crate) fn type_functions(&self) -> Vec<super::query::Function> {
        self.types.borrow().functions()
    }

    pub(crate) fn integer_bitwise(
        &self,
        operation: super::bitwise::Operation,
        values: Vec<Term>,
        span: SpanId,
    ) -> Result<Term, VcRefusal> {
        self.types
            .borrow_mut()
            .integer_bitwise(operation, values)
            .ok_or_else(|| {
                refusal(
                    "bitwise",
                    "an ordinary bitwise operand without integer sort",
                    span,
                )
            })
    }

    pub(super) fn with_template_vocabulary<R>(
        &self,
        read: impl FnOnce(&Vocabulary, usize) -> R,
    ) -> R {
        let types = self.types.borrow();
        let nominal_count = self.nominal_types.borrow().types.len();
        read(&types, nominal_count)
    }

    pub(crate) fn native_value(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        value: Val,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let native = match env.projection_work() {
            Some(work) => self.shape_with_work(ty, env.owner(), span, work)?,
            None => self.shape(ty, env.owner(), span)?,
        };
        if value.matches(&native) {
            return Ok(value);
        }
        self.coerce_value(
            &native,
            &match env.projection_work() {
                Some(work) => self.poly_shape_with_work(ty, env.owner(), span, work)?,
                None => self.poly_shape(ty, env.owner(), span)?,
            },
            env,
            value,
            false,
            span,
        )
    }

    fn coerce_value(
        &self,
        native: &Shape,
        boxed: &Shape,
        env: &TypeEnv,
        value: Val,
        boxing: bool,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        match (native, boxed, value) {
            (Shape::Leaf(leaf), Shape::Leaf(LeafTy::Poly(index)), Val::Leaf(value)) => {
                if leaf.sort() == Sort::Poly && value.sort() == Sort::Poly {
                    return Ok(Val::Leaf(value));
                }
                let mut types = self.types.borrow_mut();
                let recipe = types
                    .recipe(*index)
                    .cloned()
                    .ok_or_else(|| refusal("generic-box", "an unknown coercion recipe", span))?;
                let argument = match env.projection_work() {
                    Some(work) => types.argument_with_allocation_work(&recipe, env, work, span)?,
                    None => types.argument(&recipe, env),
                }.ok_or_else(|| refusal("generic-box", "a coercion outside its binder scope", span))?;
                let argument = match env.projection_work() {
                    Some(work) => {
                        let mut remaining = work.get();
                        let actual = types.canonical_argument(argument, &mut remaining);
                        work.set(remaining);
                        actual.ok_or_else(|| refusal("generic-box", "coercion normalization exhausted original work", span))?
                    }
                    None => argument,
                };
                let identity = argument.identity().clone();
                let result = if boxing {
                    types.box_value(leaf.sort(), identity, leaf.bounds(), value)
                } else {
                    types.unbox_value(leaf.sort(), identity, leaf.bounds(), value)
                };
                result
                    .map(Val::Leaf)
                    .ok_or_else(|| refusal("generic-box", "incompatible coercion sorts", span))
            }
            (Shape::Node(native), Shape::Node(boxed), Val::Node(values))
                if native.len() == boxed.len() && native.len() == values.len() =>
            {
                native
                    .iter()
                    .zip(boxed)
                    .zip(values)
                    .map(|((native, boxed), value)| {
                        self.coerce_value(native, boxed, env, value, boxing, span)
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map(Val::Node)
            }
            _ => Err(refusal(
                "generic-box",
                "incompatible product coercion layouts",
                span,
            )),
        }
    }

    pub(crate) fn bridge_axioms(&self, roots: &[&Term], budget: &mut usize) -> Option<Vec<Term>> {
        self.types.borrow_mut().bridge_axioms(roots, budget)
    }

    pub(crate) fn nominal_types(&self) -> Vec<Ty> {
        self.nominal_types.borrow().types.clone()
    }

    fn nominal_leaf(&self, ty: &Ty, span: SpanId) -> Result<Shape, VcRefusal> {
        // Boxed generic-type membership is a separate producer prerequisite.
        // Do not infer an inhabited monomorphic sort for a still-generic
        // opaque type merely from its Rust signature.
        if ty.has_param() {
            return Err(refusal(
                "opaque-generic-carrier",
                "an opaque carrier with uninstantiated type arguments",
                span,
            ));
        }
        let mut types = self.nominal_types.borrow_mut();
        let index = match types.indices.get(ty).copied() {
            Some(index) => index,
            None => {
                let index = u32::try_from(types.types.len()).map_err(|_| {
                    refusal("vcgen-internal", "too many nominal carrier sorts", span)
                })?;
                types.types.push(ty.clone());
                types.indices.insert(ty.clone(), index);
                index
            }
        };
        Ok(Shape::Leaf(LeafTy::Nominal(index)))
    }

    fn shape_inner(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
        depth: u32,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Shape, VcRefusal> {
        // Struct nesting is finite in well-formed VcIR (there is no
        // indirection); the bound only stops a malformed cycle.
        if depth > 64 {
            return Err(refusal("type", "a data type nested too deeply", span));
        }
        match ty {
            Ty::Bool => Ok(Shape::Leaf(LeafTy::Bool)),
            Ty::Int(range) => match supported_range(concrete_range(*range, self.pointer_width)) {
                Ok(()) => Ok(Shape::Leaf(LeafTy::Int(concrete_range(
                    *range,
                    self.pointer_width,
                )))),
                Err((tag, detail)) => Err(refusal(tag, detail, span)),
            },
            Ty::Unit => Ok(Shape::Node(Vec::new())),
            Ty::Tuple(elems) => {
                let mut children = Vec::new();
                for elem in elems {
                    children.push(self.shape_inner(elem, owner, span, depth + 1, work)?);
                }
                Ok(Shape::Node(children))
            }
            Ty::Adt(id, args) => {
                let Some(adt) = self.adts.get(id) else {
                    return Err(refusal("vcgen-internal", "an unknown data type", span));
                };
                if adt.kind == AdtKind::Opaque {
                    if !adt.variants.is_empty() {
                        return Err(refusal(
                            "vcgen-internal",
                            "an opaque carrier exposes variants",
                            span,
                        ));
                    }
                    if ty.has_param() {
                        return self.poly_shape_inner(ty, owner, span, &mut 64, work);
                    }
                    return self.nominal_leaf(ty, span);
                }
                if adt.kind == AdtKind::Enum {
                    self.register_enum_with_work(*id, span, work)?;
                    return self.poly_shape_inner(ty, owner, span, &mut 64, work);
                }
                let Some(variant) = adt.variants.first() else {
                    return Err(refusal(
                        "vcgen-internal",
                        "a struct without a variant",
                        span,
                    ));
                };
                let mut children = Vec::new();
                for field in &variant.fields {
                    children.push(self.shape_inner(
                        &self.field_type(&field.ty, args, work, span)?,
                        owner,
                        span,
                        depth + 1,
                        work,
                    )?);
                }
                Ok(Shape::Node(children))
            }
            Ty::Ref { inner, .. } => self.shape_inner(inner, owner, span, depth + 1, work),
            Ty::Param(_) | Ty::Projection(..) | Ty::MutRef(_) => self.poly_shape_inner(ty, owner, span, &mut 64, work),
        }
    }
}

/// A refusal with the given tag.
pub(crate) fn refusal(tag: &'static str, detail: impl Into<String>, span: SpanId) -> VcRefusal {
    VcRefusal {
        tag,
        detail: detail.into(),
        span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounds_of_supported_types() {
        assert_eq!(range_bounds(IntRange::U(8)), (Some(0), Some(255)));
        assert_eq!(range_bounds(IntRange::I(8)), (Some(-128), Some(127)));
        assert_eq!(
            range_bounds(IntRange::I(64)),
            (
                Some(i128::from(i64::MIN)),
                Some(u128::from(i64::MAX as u64))
            )
        );
        assert_eq!(
            range_bounds(IntRange::U(64)),
            (Some(0), Some(u128::from(u64::MAX)))
        );
        assert_eq!(range_bounds(IntRange::Nat), (Some(0), None));
        assert_eq!(range_bounds(IntRange::Int), (None, None));
        assert!(supported_range(IntRange::U(128)).is_ok());
        assert_eq!(range_bounds(IntRange::U(128)), (Some(0), Some(u128::MAX)));
        assert_eq!(
            range_bounds(IntRange::I(128)),
            (Some(i128::MIN), Some(i128::MAX as u128))
        );
        assert!(supported_range(IntRange::USize).is_ok());
        assert!(supported_range(IntRange::Char).is_err());
    }
}
