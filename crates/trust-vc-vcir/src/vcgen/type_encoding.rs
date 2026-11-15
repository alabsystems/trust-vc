//! Declaration-scoped type arguments and the boxed value vocabulary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{AdtId, FnId, IntRange, Ty};

use super::query::Function;
use super::term::{Sort, Term};

mod bridges;
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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TypeEnv {
    owner: Option<FnId>,
    arguments: Vec<TypeArgument>,
}

impl TypeEnv {
    pub(crate) fn new(owner: FnId, arguments: Vec<TypeArgument>) -> Self {
        Self {
            owner: Some(owner),
            arguments,
        }
    }

    pub(crate) fn owner(&self) -> Option<FnId> {
        self.owner
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
    SharedRef(Box<TypeRecipe>),
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
    fn closed(&self) -> bool {
        match self {
            Self::Parameter { .. } | Self::ProductParameter { .. } => false,
            Self::Tuple(args)
            | Self::Opaque(_, args)
            | Self::Struct(_, args)
            | Self::Enum(_, args) => args.iter().all(Self::closed),
            Self::SharedRef(inner) => inner.closed(),
            Self::Bool | Self::Int(_) | Self::Unit => true,
        }
    }

    /// The caller supplies actual admitted ADT declarations, never names.
    pub(crate) fn registered(
        ty: &Ty,
        owner: Option<FnId>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
    ) -> Option<Self> {
        Self::registered_with_work(ty, owner, adts, &mut 64)
    }

    pub(crate) fn registered_with_work(
        ty: &Ty,
        owner: Option<FnId>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        left: &mut usize,
    ) -> Option<Self> {
        Self::visit(ty, owner.map(RecipeOwner::Function), adts, left)
    }

    pub(crate) fn product_field(
        ty: &Ty,
        owner: ProductFamily,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
        left: &mut usize,
    ) -> Option<Self> {
        Self::visit(ty, Some(RecipeOwner::Product(owner)), adts, left)
    }

    fn visit(
        ty: &Ty,
        owner: Option<RecipeOwner>,
        adts: &impl Fn(AdtId) -> Option<RecipeAdt>,
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
                        .map(|arg| Self::visit(arg, owner, adts, left))
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
                    .map(|arg| Self::visit(arg, owner, adts, left))
                    .collect::<Option<_>>()?;
                match admitted {
                    RecipeAdt::Opaque(_) => Self::Opaque(*id, args),
                    RecipeAdt::Struct(_) => Self::Struct(*id, args),
                    RecipeAdt::Enum(_) => Self::Enum(*id, args),
                }
            }
            Ty::Ref {
                mutable: false,
                inner,
            } => Self::SharedRef(Box::new(Self::visit(inner, owner, adts, left)?)),
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
    functions: BTreeMap<String, Function>,
    bridges: bridges::Bridges,
    products: products::Products,
    sums: sums::Sums,
}

impl Vocabulary {
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
        let argument = self.argument_in(recipe, env, None)?;
        if recipe.closed() {
            self.closed_arguments.insert(argument.clone());
        }
        Some(argument)
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
    ) -> Option<TypeArgument> {
        if let TypeRecipe::Parameter { owner, index } = recipe {
            return (env.owner() == Some(*owner))
                .then(|| env.get(*index).cloned())
                .flatten();
        }
        if let TypeRecipe::ProductParameter { owner, index } = recipe {
            let (actual, args) = product?;
            return (*owner == actual)
                .then(|| args.get(*index as usize).cloned())
                .flatten();
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
                    terms.extend(self.argument_in(arg, env, product)?.terms());
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
                    terms.extend(self.argument_in(arg, env, product)?.terms());
                }
                self.call(format!("ty_adt{index}"), terms, Sort::TypeId)
            }
            TypeRecipe::SharedRef(inner) => {
                let inner = self.argument_in(inner, env, product)?;
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
