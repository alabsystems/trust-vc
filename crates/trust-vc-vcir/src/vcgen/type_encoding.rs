//! Declaration-scoped type arguments and the boxed value vocabulary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{AdtId, FnId, IntRange, ProjectionId, Ty};

use super::query::Function;
use super::term::{Sort, Term};

mod bridges;
mod mut_refs;
mod products;
mod sums;
#[cfg(test)]
mod tests;

/// A decoration and underlying type identity, with distinct solver sorts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypeArgument {
    decoration: Term,
    identity: Term,
}

impl TypeArgument {
    pub(crate) fn named(decoration: String, identity: String) -> Self {
        Self {
            decoration: Term::var(decoration, Sort::Decoration),
            identity: Term::var(identity, Sort::TypeId),
        }
    }

    pub(crate) fn new(decoration: Term, identity: Term) -> Option<Self> {
        (decoration.sort() == Sort::Decoration && identity.sort() == Sort::TypeId).then_some(Self {
            decoration,
            identity,
        })
    }

    pub(super) fn terms_ref(&self) -> [&Term; 2] {
        [&self.decoration, &self.identity]
    }

    pub(crate) fn identity(&self) -> &Term {
        &self.identity
    }

    pub(crate) fn terms(&self) -> [Term; 2] {
        [self.decoration.clone(), self.identity.clone()]
    }
}

/// A binder environment, never a crate-global table of bare parameter numbers.
#[derive(Debug, Clone, Default)]
pub(crate) struct TypeEnv {
    owner: Option<FnId>,
    // Sharing the immutable vector makes a context clone independent of the
    // expanded projection-term size. There is no mutation/lookup capability.
    arguments: std::rc::Rc<Vec<TypeArgument>>,
    projection_work: Option<std::rc::Rc<std::cell::Cell<usize>>>,
}

impl PartialEq for TypeEnv {
    fn eq(&self, other: &Self) -> bool {
        self.owner == other.owner && self.arguments == other.arguments
    }
}
impl Eq for TypeEnv {}

impl TypeEnv {
    pub(crate) fn retain_work(&mut self, work: &std::rc::Rc<std::cell::Cell<usize>>) {
        self.projection_work.get_or_insert_with(|| work.clone());
    }
    pub(crate) fn new(owner: FnId, arguments: Vec<TypeArgument>) -> Self {
        Self {
            owner: Some(owner),
            arguments: std::rc::Rc::new(arguments),
            projection_work: None,
        }
    }

    pub(crate) fn owner(&self) -> Option<FnId> {
        self.owner
    }

    pub(crate) fn projection_work(&self) -> Option<&std::rc::Rc<std::cell::Cell<usize>>> {
        self.projection_work.as_ref()
    }

    pub(crate) fn get(&self, index: u32) -> Option<&TypeArgument> {
        self.owner?;
        self.arguments.get(index as usize)
    }

    pub(crate) fn terms(&self) -> Vec<Term> {
        self.arguments
            .iter()
            .flat_map(TypeArgument::terms)
            .collect()
    }

    pub(crate) fn len(&self) -> usize {
        self.arguments.len()
    }
}

/// A type expression interpreted only inside an explicit binder environment.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypeRecipe {
    Parameter { owner: FnId, index: u32 },
    ProductParameter { owner: ProductFamily, index: u32 },
    Bool,
    Int(IntRange),
    Unit,
    Tuple(Vec<TypeRecipe>),
    Opaque(AdtId, Vec<TypeRecipe>),
    Struct(AdtId, Vec<TypeRecipe>),
    Enum(AdtId, Vec<TypeRecipe>),
    Projection(ProjectionId, Vec<TypeRecipe>),
    SharedRef(Box<TypeRecipe>),
    MutRef(Box<TypeRecipe>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ProductFamily {
    Unit,
    Tuple(u32),
    Struct(AdtId),
    Enum(AdtId),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecipeAdt {
    Opaque(usize),
    Struct(usize),
    Enum(usize),
}

#[derive(Clone, Copy)]
enum RecipeOwner {
    Function(FnId),
    Product(ProductFamily),
}

impl TypeRecipe {
    pub(in crate::vcgen) fn has_projection(&self) -> bool {
        match self {
            Self::Projection(..) => true,
            Self::Tuple(args) | Self::Opaque(_, args) | Self::Struct(_, args)
            | Self::Enum(_, args) => args.iter().any(Self::has_projection),
            Self::SharedRef(inner) | Self::MutRef(inner) => inner.has_projection(),
            _ => false,
        }
    }

    fn closed(&self) -> bool {
        match self {
            Self::Parameter { .. } | Self::ProductParameter { .. } => false,
            Self::Tuple(args)
            | Self::Opaque(_, args)
            | Self::Struct(_, args)
            | Self::Enum(_, args)
            | Self::Projection(_, args) => args.iter().all(Self::closed),
            Self::SharedRef(inner) | Self::MutRef(inner) => inner.closed(),
            Self::Bool | Self::Int(_) | Self::Unit => true,
        }
    }

    /// The caller supplies actual admitted ADT declarations, never names.
    pub(crate) fn registered(
        ty: &Ty,
        owner: Option<FnId>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        projections: &impl Fn(ProjectionId) -> Option<usize>,
    ) -> Option<Self> {
        Self::registered_with_work(ty, owner, adts, projections, &mut 64)
    }

    pub(crate) fn registered_with_work(
        ty: &Ty,
        owner: Option<FnId>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        projections: &impl Fn(ProjectionId) -> Option<usize>,
        left: &mut usize,
    ) -> Option<Self> {
        Self::visit(ty, owner.map(RecipeOwner::Function), adts, projections, left)
    }

    pub(crate) fn product_field(
        ty: &Ty,
        owner: ProductFamily,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        projections: &impl Fn(ProjectionId) -> Option<usize>,
        left: &mut usize,
    ) -> Option<Self> {
        Self::visit(ty, Some(RecipeOwner::Product(owner)), adts, projections, left)
    }

    fn visit(
        ty: &Ty,
        owner: Option<RecipeOwner>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        projections: &impl Fn(ProjectionId) -> Option<usize>,
        left: &mut usize,
    ) -> Option<Self> {
        *left = left.checked_sub(1)?;
        Some(match ty {
            Ty::Param(index) => match owner? {
                RecipeOwner::Function(owner) => Self::Parameter {
                    owner,
                    index: *index,
                },
                RecipeOwner::Product(owner) => Self::ProductParameter {
                    owner,
                    index: *index,
                },
            },
            Ty::Bool => Self::Bool,
            Ty::Int(range) if super::val::supported_range(*range).is_ok() => Self::Int(*range),
            Ty::Unit => Self::Unit,
            Ty::Tuple(args) => {
                if args.is_empty() || args.len() > *left {
                    return None;
                }
                Self::Tuple(
                    args.iter()
                        .map(|arg| Self::visit(arg, owner, adts, projections, left))
                        .collect::<Option<_>>()?,
                )
            }
            Ty::Adt(id, args) => {
                let admitted = adts(*id)?;
                let (RecipeAdt::Opaque(arity) | RecipeAdt::Struct(arity) | RecipeAdt::Enum(arity)) =
                    admitted;
                if arity != args.len() || args.len() > *left {
                    return None;
                }
                let args = args
                    .iter()
                    .map(|arg| Self::visit(arg, owner, adts, projections, left))
                    .collect::<Option<_>>()?;
                match admitted {
                    RecipeAdt::Opaque(_) => Self::Opaque(*id, args),
                    RecipeAdt::Struct(_) => Self::Struct(*id, args),
                    RecipeAdt::Enum(_) => Self::Enum(*id, args),
                }
            }
            Ty::Projection(id, args) => {
                let arity = projections(*id)?;
                if arity == 0 || arity != args.len() || args.len() > *left {
                    return None;
                }
                Self::Projection(
                    *id,
                    args.iter()
                        .map(|arg| Self::visit(arg, owner, adts, projections, left))
                        .collect::<Option<_>>()?,
                )
            }
            Ty::Ref {
                mutable: false,
                inner,
            } => Self::SharedRef(Box::new(Self::visit(inner, owner, adts, projections, left)?)),
            Ty::MutRef(inner) => {
                Self::MutRef(Box::new(Self::visit(inner, owner, adts, projections, left)?))
            }
            _ => return None,
        })
    }
}

/// Typed declarations used by a crate's type recipes and concrete bridges.
#[derive(Default)]
pub(crate) struct Vocabulary {
    recipes: Vec<TypeRecipe>,
    closed_arguments: HashSet<TypeArgument>,
    recipe_indices: HashMap<TypeRecipe, u32>,
    opaque_indices: HashMap<AdtId, u32>,
    adt_recipes: HashMap<AdtId, RecipeAdt>,
    projection_indices: HashMap<ProjectionId, u32>,
    projection_arities: HashMap<ProjectionId, usize>,
    projection_symbols: std::rc::Rc<HashSet<String>>,
    projection_reductions: HashMap<String, HashMap<Vec<Term>, Term>>,
    functions: BTreeMap<String, Function>,
    bridges: bridges::Bridges,
    products: products::Products,
    sums: sums::Sums,
    mut_refs: mut_refs::MutRefs,
}

impl Vocabulary {
    pub(crate) fn register_projection_declaration(&mut self, id: ProjectionId, arity: usize) -> Option<()> {
        if arity == 0 || self.projection_arities.get(&id).is_some_and(|old| *old != arity) { return None; }
        self.projection_arities.insert(id, arity);
        Some(())
    }
    pub(crate) fn register_projection_definition(
        &mut self, id: ProjectionId, arguments: &[TypeArgument], result: &TypeArgument,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::expr::R<()> {
        if arguments.is_empty() || self.projection_arities.get(&id).is_some_and(|arity| *arity != arguments.len()) {
            return Err(super::val::refusal("projection-definition", "associated implementation arity disagrees", span));
        }
        self.projection_arities.insert(id, arguments.len());
        let next = u32::try_from(self.projection_indices.len()).map_err(|_| super::val::refusal("projection-definition", "too many associated constructors", span))?;
        let index = *self.projection_indices.entry(id).or_insert(next);
        super::inline_work::items(work, arguments.len(), span)?;
        for argument in arguments {
            // Five owned copies (flatten, two signatures, two rule keys),
            // plus hash/equality at both rule lookups/insertions.
            for term in argument.terms_ref() { super::inline_work::term(work, term, 9, span)?; }
        }
        for term in result.terms_ref() { super::inline_work::term(work, term, 2, span)?; }
        let inputs: Vec<_> = arguments.iter().flat_map(TypeArgument::terms).collect();
        for (name, value, sort) in [
            (format!("ty_projection_dec{index}"), &result.decoration, Sort::Decoration),
            (format!("ty_projection{index}"), &result.identity, Sort::TypeId),
        ] {
            let _ = self.call(name.clone(), inputs.clone(), sort);
            std::rc::Rc::make_mut(&mut self.projection_symbols).insert(name.clone());
            let rules = self.projection_reductions.entry(name).or_default();
            if rules.get(&inputs).is_some_and(|previous| previous != value) {
                return Err(super::val::refusal("projection-definition", "ambiguous associated implementation", span));
            }
            rules.insert(inputs.clone(), value.clone());
        }
        Ok(())
    }

    /// Interpret private type constructors under their represented closed
    /// implementation semantics. No equality fact or axiom is emitted.
    pub(crate) fn canonical_type_terms(&self, term: Term, work: &mut usize) -> Option<Term> {
        self.canonical_type_terms_at(term, work, 0)
    }

    pub(crate) fn canonical_argument(&self, argument: TypeArgument, work: &mut usize) -> Option<TypeArgument> {
        TypeArgument::new(self.canonical_type_terms(argument.decoration, work)?,
            self.canonical_type_terms(argument.identity, work)?)
    }

    fn canonical_type_terms_at(&self, term: Term, work: &mut usize, depth: usize) -> Option<Term> {
        if self.projection_reductions.is_empty() { return Some(term); }
        let cost = match &term { Term::Call { name, .. } | Term::Var { name, .. } => name.len() + 1, _ => 1 };
        *work = work.checked_sub(cost)?;
        if depth >= 256 { *work = 0; return None; }
        let child = |term, work: &mut usize| self.canonical_type_terms_at(term, work, depth + 1);
        Some(match term {
            Term::Call { name, args, sort } => {
                *work = work.checked_sub(args.len())?;
                let args = args.into_iter().map(|term| child(term, work)).collect::<Option<Vec<_>>>()?;
                if let Some(rules) = self.projection_reductions.get(&name) {
                    let empty = HashMap::new();
                    // Preprice hash/equality of complete ordered type pairs.
                    for argument in &args {
                        super::substitution::price(argument, &empty, work)?;
                        super::substitution::price(argument, &empty, work)?;
                    }
                    if let Some(value) = rules.get(&args) {
                        if value.sort() != sort { return None; }
                        return super::substitution::apply(value, &empty, work);
                    }
                }
                Term::Call { name, args, sort }
            }
            Term::Not(value) => !child(*value, work)?,
            Term::Neg(value) => -child(*value, work)?,
            Term::And(values) => {
                *work = work.checked_sub(values.len())?;
                Term::and(values.into_iter().map(|value| child(value, work)).collect::<Option<Vec<_>>>()?)
            }
            Term::Or(values) => {
                *work = work.checked_sub(values.len())?;
                Term::or(values.into_iter().map(|value| child(value, work)).collect::<Option<Vec<_>>>()?)
            }
            Term::Implies(a, b) => Term::implies(child(*a, work)?, child(*b, work)?),
            Term::Cmp(op, a, b) => {
                let (a, b) = (child(*a, work)?, child(*b, work)?);
                match op { super::term::CmpOp::Eq => Term::eq(a, b), super::term::CmpOp::Lt => Term::lt(a, b), super::term::CmpOp::Le => Term::le(a, b) }
            }
            Term::Arith(op, a, b) => Term::arith(op, child(*a, work)?, child(*b, work)?),
            Term::Ite(a, b, c, _) => Term::ite(child(*a, work)?, child(*b, work)?, child(*c, work)?),
            other => other,
        })
    }

    pub(crate) fn environment(
        &self,
        owner: FnId,
        arguments: Vec<TypeArgument>,
        work: &std::rc::Rc<std::cell::Cell<usize>>,
    ) -> TypeEnv {
        let projected = arguments.iter().any(|argument| argument.terms_ref().iter()
            .any(|term| Self::has_projection_term(term, &self.projection_symbols)));
        let mut environment = TypeEnv::new(owner, arguments);
        if projected { environment.projection_work = Some(work.clone()); }
        environment
    }

    pub(crate) fn intern(&mut self, recipe: TypeRecipe) -> Option<u32> {
        if let Some(index) = self.recipe_indices.get(&recipe) {
            return Some(*index);
        }
        let index = u32::try_from(self.recipes.len()).ok()?;
        self.recipe_indices.insert(recipe.clone(), index);
        self.recipes.push(recipe);
        Some(index)
    }

    pub(crate) fn recipe(&self, index: u32) -> Option<&TypeRecipe> {
        self.recipes.get(index as usize)
    }

    pub(crate) fn functions(&self) -> Vec<Function> {
        self.functions.values().cloned().collect()
    }

    fn call(&mut self, name: String, args: Vec<Term>, ret: Sort) -> Term {
        let signature = Function {
            name: name.clone(),
            params: args.iter().map(Term::sort).collect(),
            ret,
        };
        self.functions.entry(name.clone()).or_insert(signature);
        Term::call(name, args, ret)
    }

    pub(crate) fn argument(&mut self, recipe: &TypeRecipe, env: &TypeEnv) -> Option<TypeArgument> {
        // These legacy value/layout callers have no retained caller work cell.
        // A projected recipe, including one forwarded through a parameter,
        // cannot use this path to make unpriced copies of projection terms.
        if recipe.has_projection() { return None; }
        let symbols = self.projection_symbols.clone();
        self.argument_priced(recipe, env, &mut |term, _| {
            !Self::has_projection_term(term, &symbols)
        })
    }

    pub(crate) fn argument_with_work(
        &mut self,
        recipe: &TypeRecipe,
        env: &TypeEnv,
        work: &std::cell::Cell<usize>,
        span: crate::SpanId,
    ) -> super::expr::R<Option<TypeArgument>> {
        let work = env.projection_work().map_or(work, |original| original.as_ref());
        if !self.requires_projection_work(recipe, env) && env.projection_work().is_none() {
            return Ok(self.argument(recipe, env));
        }
        self.argument_with_allocation_work(recipe, env, work, span)
    }

    pub(crate) fn argument_with_allocation_work(
        &mut self, recipe: &TypeRecipe, env: &TypeEnv, work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::expr::R<Option<TypeArgument>> {
        let work = env.projection_work().map_or(work, |original| original.as_ref());
        let mut failure = None;
        let mut price = |term: &Term, copies| match super::inline_work::term(work, term, copies, span) {
            Ok(()) => true,
            Err(error) => { failure = Some(error); false }
        };
        let result = self.argument_priced(recipe, env, &mut price);
        drop(price);
        match failure {
            Some(error) => Err(error),
            None => Ok(result),
        }
    }

    pub(in crate::vcgen) fn requires_projection_work(&self, recipe: &TypeRecipe, env: &TypeEnv) -> bool {
        match recipe {
            TypeRecipe::Projection(..) => true,
            TypeRecipe::Parameter { owner, index } if env.owner() == Some(*owner) => {
                env.get(*index).is_some_and(|argument| {
                    argument.terms_ref().iter().any(|term| {
                        Self::has_projection_term(term, &self.projection_symbols)
                    })
                })
            }
            TypeRecipe::Tuple(args) | TypeRecipe::Opaque(_, args)
            | TypeRecipe::Struct(_, args) | TypeRecipe::Enum(_, args) => {
                args.iter().any(|arg| self.requires_projection_work(arg, env))
            }
            TypeRecipe::SharedRef(inner) | TypeRecipe::MutRef(inner) => {
                self.requires_projection_work(inner, env)
            }
            _ => false,
        }
    }

    fn argument_priced(
        &mut self,
        recipe: &TypeRecipe,
        env: &TypeEnv,
        price: &mut dyn FnMut(&Term, usize) -> bool,
    ) -> Option<TypeArgument> {
        let argument = self.argument_in(recipe, env, None, price)?;
        if recipe.closed() {
            if !Self::price_argument(&argument, price) { return None; }
            self.closed_arguments.insert(argument.clone());
        }
        Some(argument)
    }

    fn argument_unmetered_in(
        &mut self,
        recipe: &TypeRecipe,
        env: &TypeEnv,
        product: Option<(ProductFamily, &[TypeArgument])>,
    ) -> Option<TypeArgument> {
        if recipe.has_projection() { return None; }
        let symbols = self.projection_symbols.clone();
        self.argument_in(recipe, env, product, &mut |term, _| {
            !Self::has_projection_term(term, &symbols)
        })
    }

    fn price_argument(argument: &TypeArgument, price: &mut dyn FnMut(&Term, usize) -> bool) -> bool {
        argument.terms_ref().iter().all(|term| price(term, 1))
    }

    // This table classifies only private, already-generated type-constructor
    // applications for a refusal. It never selects native items or grants a
    // type, value, source capability, body, Copy or ownership permission.
    fn has_projection_term(term: &Term, symbols: &HashSet<String>) -> bool {
        if symbols.is_empty() { return false; }
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term {
                Term::Call { name, .. } if symbols.contains(name) => return true,
                Term::Call { args, .. } | Term::And(args) | Term::Or(args) => pending.extend(args),
                Term::Not(inner) | Term::Neg(inner) => pending.push(inner),
                Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
                    pending.push(a); pending.push(b);
                }
                Term::Ite(a, b, c, _) => { pending.push(a); pending.push(b); pending.push(c); }
                Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
            }
        }
        false
    }

    pub(super) fn closed_arguments(&self) -> &HashSet<TypeArgument> {
        &self.closed_arguments
    }

    pub(super) fn template_functions(&self) -> impl Iterator<Item = &Function> {
        self.functions.values()
    }

    fn argument_in(
        &mut self,
        recipe: &TypeRecipe,
        env: &TypeEnv,
        product: Option<(ProductFamily, &[TypeArgument])>,
        price: &mut dyn FnMut(&Term, usize) -> bool,
    ) -> Option<TypeArgument> {
        if let TypeRecipe::Parameter { owner, index } = recipe {
            if env.owner() != Some(*owner) { return None; }
            let argument = env.get(*index)?;
            return Self::price_argument(argument, price).then(|| argument.clone());
        }
        if let TypeRecipe::ProductParameter { owner, index } = recipe {
            let (actual, args) = product?;
            if *owner != actual { return None; }
            let argument = args.get(*index as usize)?;
            return Self::price_argument(argument, price).then(|| argument.clone());
        }
        let nil = self.call("ty_dec_nil".into(), vec![], Sort::Decoration);
        let identity = match recipe {
            TypeRecipe::Parameter { .. } | TypeRecipe::ProductParameter { .. } => return None,
            TypeRecipe::Bool => self.call("ty_bool".into(), vec![], Sort::TypeId),
            TypeRecipe::Int(range) => {
                let suffix = match range {
                    IntRange::Int => "int".into(),
                    IntRange::Nat => "nat".into(),
                    IntRange::U(bits) => format!("u{bits}"),
                    IntRange::I(bits) => format!("i{bits}"),
                    IntRange::USize => "usize".into(),
                    IntRange::ISize => "isize".into(),
                    _ => return None,
                };
                self.call(format!("ty_{suffix}"), vec![], Sort::TypeId)
            }
            TypeRecipe::Unit => self.call("ty_unit".into(), vec![], Sort::TypeId),
            TypeRecipe::Tuple(args) => {
                let mut terms = Vec::new();
                for arg in args {
                    let argument = self.argument_in(arg, env, product, price)?;
                    if !Self::price_argument(&argument, price) { return None; }
                    terms.extend(argument.terms());
                }
                self.call(format!("ty_tuple{}", args.len()), terms, Sort::TypeId)
            }
            TypeRecipe::Opaque(id, args)
            | TypeRecipe::Struct(id, args)
            | TypeRecipe::Enum(id, args) => {
                let descriptor = match recipe {
                    TypeRecipe::Opaque(..) => RecipeAdt::Opaque(args.len()),
                    TypeRecipe::Struct(..) => RecipeAdt::Struct(args.len()),
                    TypeRecipe::Enum(..) => RecipeAdt::Enum(args.len()),
                    _ => return None,
                };
                if self
                    .adt_recipes
                    .get(id)
                    .is_some_and(|old| *old != descriptor)
                {
                    return None;
                }
                self.adt_recipes.insert(*id, descriptor);
                let next = u32::try_from(self.opaque_indices.len()).ok()?;
                let index = *self.opaque_indices.entry(*id).or_insert(next);
                let mut terms = Vec::new();
                for arg in args {
                    let argument = self.argument_in(arg, env, product, price)?;
                    if !Self::price_argument(&argument, price) { return None; }
                    terms.extend(argument.terms());
                }
                self.call(format!("ty_adt{index}"), terms, Sort::TypeId)
            }
            TypeRecipe::Projection(id, args) => {
                if args.is_empty()
                    || self.projection_arities.get(id).is_some_and(|arity| *arity != args.len())
                {
                    return None;
                }
                self.projection_arities.insert(*id, args.len());
                let next = u32::try_from(self.projection_indices.len()).ok()?;
                let index = *self.projection_indices.entry(*id).or_insert(next);
                let mut terms = Vec::new();
                for arg in args {
                    let argument = self.argument_in(arg, env, product, price)?;
                    if !Self::price_argument(&argument, price) { return None; }
                    terms.extend(argument.terms());
                }
                // A projection has both its own decoration and underlying
                // identity, applied to every ordered argument's two identities.
                // Neither function is an ADT layout or a type-equality axiom.
                if !terms.iter().all(|term| price(term, 1)) { return None; }
                let decoration_name = format!("ty_projection_dec{index}");
                let identity_name = format!("ty_projection{index}");
                std::rc::Rc::make_mut(&mut self.projection_symbols).insert(decoration_name.clone());
                std::rc::Rc::make_mut(&mut self.projection_symbols).insert(identity_name.clone());
                let decoration = self.call(decoration_name, terms.clone(), Sort::Decoration);
                let identity = self.call(
                    identity_name, terms, Sort::TypeId,
                );
                return TypeArgument::new(decoration, identity);
            }
            TypeRecipe::MutRef(inner) => {
                let inner = self.argument_in(inner, env, product, price)?;
                if !Self::price_argument(&inner, price) { return None; }
                let identity = self.call("ty_mut_ref".into(), inner.terms().into_iter().collect(), Sort::TypeId);
                if !price(&identity, 1) { return None; }
                self.mut_refs.types.insert(identity.clone(), inner);
                identity
            }
            TypeRecipe::SharedRef(inner) => {
                let inner = self.argument_in(inner, env, product, price)?;
                let decoration = self.call(
                    "ty_dec_ref".into(),
                    vec![inner.decoration],
                    Sort::Decoration,
                );
                return TypeArgument::new(decoration, inner.identity);
            }
        };
        TypeArgument::new(nil, identity)
    }

    pub(crate) fn membership(&mut self, value: Term, identity: Term) -> Option<Term> {
        if value.sort() != Sort::Poly || identity.sort() != Sort::TypeId {
            return None;
        }
        Some(self.call("has_type".into(), vec![value, identity], Sort::Bool))
    }
}
