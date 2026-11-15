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

use crate::ids::{AdtId, FnId, SpanId};
use crate::item::{AdtDecl, AdtKind, DefOrder, FnDecl, RecGroup, VcCrate};
use crate::ty::{IntRange, Ty};

use super::query::VcRefusal;
use super::term::{Sort, Term};
use super::type_encoding::{
    ProductFamily, RecipeAdt, TypeArgument, TypeEnv, TypeRecipe, Vocabulary,
};

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

/// Lookup tables shared by everything the generator does for one crate.
pub(crate) struct Ctx<'a> {
    pub(crate) pointer_width: u32,
    pub(crate) architecture: crate::bitvector::Architecture,
    pub(crate) fns: HashMap<FnId, &'a FnDecl>,
    validated_instances: std::collections::HashSet<FnId>,
    pub(crate) adts: HashMap<AdtId, &'a AdtDecl>,
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
    pub(crate) fn new(krate: &'a VcCrate) -> Self {
        Self::for_width(krate, krate.pointer_width)
    }

    pub(crate) fn for_width(krate: &'a VcCrate, pointer_width: u32) -> Self {
        let fns: HashMap<_, _> = krate.fns.iter().map(|decl| (decl.id, decl)).collect();
        let validated_instances = crate::instance_semantics::validated_origins(&fns);
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
            pointer_width,
            architecture: krate.architecture,
            fns,
            validated_instances,
            adts: krate.adts.iter().map(|adt| (adt.id, adt)).collect(),
            def_order,
            groups,
            quants: std::cell::RefCell::default(),
            nominal_types: std::cell::RefCell::default(),
            types: std::cell::RefCell::default(),
        }
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
        self.shape_inner(ty, owner, span, 0)
    }

    fn type_recipe(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
    ) -> Result<TypeRecipe, VcRefusal> {
        TypeRecipe::registered(ty, owner, &|id| self.recipe_adt(id))
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

    pub(crate) fn poly_shape(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
    ) -> Result<Shape, VcRefusal> {
        self.poly_shape_inner(ty, owner, span, &mut 64)
    }

    fn poly_shape_inner(
        &self,
        ty: &Ty,
        owner: Option<FnId>,
        span: SpanId,
        left: &mut usize,
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
                self.register_enum(*id, span)?;
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
                Some(types.clone())
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
                        .map(|field| field.ty.subst(args))
                        .collect(),
                )
            }
            Ty::Ref {
                mutable: false,
                inner,
            } if matches!(inner.as_ref(), Ty::Tuple(_) | Ty::Unit)
                || matches!(inner.as_ref(), Ty::Adt(id, _) if self.adts.get(id).is_some_and(|adt| adt.kind == AdtKind::Struct)) =>
            {
                return self.poly_shape_inner(inner, owner, span, left);
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
                .map(|ty| self.poly_shape_inner(ty, owner, span, left))
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
        let LeafTy::Poly(index) = leaf else {
            return Ok(leaf.fact(term));
        };
        let mut types = self.types.borrow_mut();
        let recipe = types
            .recipe(index)
            .cloned()
            .ok_or_else(|| refusal("generic-type", "an unknown boxed type recipe", span))?;
        let argument = types.argument(&recipe, env).ok_or_else(|| {
            refusal(
                "generic-type",
                "a boxed value outside its binder scope",
                span,
            )
        })?;
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
        let native = self.shape(ty, env.owner(), span)?;
        if value.matches(&native) {
            return Ok(value);
        }
        self.coerce_value(
            &native,
            &self.poly_shape(ty, env.owner(), span)?,
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
                let identity = types
                    .argument(&recipe, env)
                    .ok_or_else(|| {
                        refusal("generic-box", "a coercion outside its binder scope", span)
                    })?
                    .identity()
                    .clone();
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
                    children.push(self.shape_inner(elem, owner, span, depth + 1)?);
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
                        return self.poly_shape(ty, owner, span);
                    }
                    return self.nominal_leaf(ty, span);
                }
                if adt.kind == AdtKind::Enum {
                    self.register_enum(*id, span)?;
                    return self.poly_shape(ty, owner, span);
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
                        &field.ty.subst(args),
                        owner,
                        span,
                        depth + 1,
                    )?);
                }
                Ok(Shape::Node(children))
            }
            Ty::Ref { inner, .. } => self.shape_inner(inner, owner, span, depth + 1),
            Ty::Param(_) => self.poly_shape(ty, owner, span),
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
