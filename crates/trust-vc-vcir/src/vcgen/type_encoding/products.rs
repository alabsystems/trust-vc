//! Typed whole-product views of the existing flattened native representation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use super::{Function, ProductFamily, Sort, Term, TypeArgument, TypeEnv, TypeRecipe, Vocabulary};

#[derive(Clone, PartialEq, Eq)]
struct Schema {
    family: ProductFamily,
    arity: usize,
    fields: Vec<TypeRecipe>,
    pack: String,
    projections: Vec<String>,
    type_constructor: String,
}

#[derive(Clone, Copy)]
enum Operation {
    Pack(usize),
    Projection(usize),
}

#[derive(Default)]
pub(super) struct Products {
    schemas: Vec<Schema>,
    families: HashMap<ProductFamily, usize>,
    operations: HashMap<String, Operation>,
    type_constructors: HashMap<String, usize>,
}

pub(super) fn field_recipe(
    recipe: &TypeRecipe,
    owner: ProductFamily,
    arity: usize,
    left: &mut usize,
) -> Option<()> {
    field_recipe_with_projections(recipe, owner, arity, left, &|_| None)
}

pub(super) fn field_recipe_with_projections(
    recipe: &TypeRecipe, owner: ProductFamily, arity: usize, left: &mut usize,
    projection: &impl Fn(crate::ProjectionId) -> Option<usize>,
) -> Option<()> {
    *left = left.checked_sub(1)?;
    match recipe {
        TypeRecipe::Parameter { .. } => None,
        TypeRecipe::Projection(id, args) => {
            if args.is_empty() || projection(*id) != Some(args.len()) { return None; }
            for argument in args { field_recipe_with_projections(argument, owner, arity, left, projection)?; }
            Some(())
        }
        TypeRecipe::ProductParameter {
            owner: actual,
            index,
        } => (*actual == owner && (*index as usize) < arity).then_some(()),
        TypeRecipe::Tuple(args)
        | TypeRecipe::Opaque(_, args)
        | TypeRecipe::Struct(_, args)
        | TypeRecipe::Enum(_, args) => {
            if args.len() > *left {
                return None;
            }
            for arg in args {
                field_recipe_with_projections(arg, owner, arity, left, projection)?;
            }
            Some(())
        }
        TypeRecipe::SharedRef(inner) | TypeRecipe::MutRef(inner) => {
            field_recipe_with_projections(inner, owner, arity, left, projection)
        }
        TypeRecipe::Int(range) => super::super::val::supported_range(*range)
            .is_ok()
            .then_some(()),
        TypeRecipe::Bool | TypeRecipe::Unit => Some(()),
    }
}

fn prefix(args: &[TypeArgument]) -> Vec<Term> {
    args.iter().flat_map(TypeArgument::terms).collect()
}

pub(super) fn arguments(terms: &[Term], arity: usize) -> Option<Vec<TypeArgument>> {
    if terms.len() != arity.checked_mul(2)? {
        return None;
    }
    terms
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| TypeArgument::new(pair[0].clone(), pair[1].clone()))
        .collect()
}

impl Vocabulary {
    pub(super) fn declare_product_function(
        &mut self,
        name: String,
        params: Vec<Sort>,
        ret: Sort,
    ) -> Option<()> {
        if let Some(previous) = self.functions.get(&name) {
            return (previous.params == params && previous.ret == ret).then_some(());
        }
        self.functions
            .insert(name.clone(), Function { name, params, ret });
        Some(())
    }

    /// Ctx supplies a finite checked declaration layout. Product parameters
    /// have their own owner domain; an unrelated FnId never stands for an ADT.
    pub(crate) fn register_product(
        &mut self,
        family: ProductFamily,
        arity: usize,
        fields: Vec<TypeRecipe>,
    ) -> Option<()> {
        self.register_product_inner(family, arity, fields, false)
    }

    pub(crate) fn register_product_with_work(
        &mut self, family: ProductFamily, arity: usize, fields: Vec<TypeRecipe>,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<()>> {
        super::super::inline_work::items(work, 1 + fields.len(), span)?;
        let mut pending: Vec<_> = fields.iter().collect();
        while let Some(recipe) = pending.pop() {
            super::super::inline_work::items(work, 1, span)?;
            match recipe {
                TypeRecipe::Tuple(args) | TypeRecipe::Opaque(_, args) | TypeRecipe::Struct(_, args)
                | TypeRecipe::Enum(_, args) | TypeRecipe::Projection(_, args) => {
                    super::super::inline_work::items(work, args.len(), span)?;
                    pending.extend(args);
                }
                TypeRecipe::SharedRef(inner) | TypeRecipe::MutRef(inner) => {
                    super::super::inline_work::items(work, 1, span)?;
                    pending.push(inner);
                }
                _ => {}
            }
        }
        Ok(self.register_product_inner(family, arity, fields, true))
    }

    fn register_product_inner(
        &mut self, family: ProductFamily, arity: usize, fields: Vec<TypeRecipe>, projected: bool,
    ) -> Option<()> {
        if arity > 64 || fields.len() > 64 {
            return None;
        }
        match family {
            ProductFamily::Enum(_) => return None,
            ProductFamily::Unit if arity != 0 || !fields.is_empty() => return None,
            ProductFamily::Tuple(n)
                if arity == 0
                    || n as usize != arity
                    || arity != fields.len()
                    || fields.iter().enumerate().any(|(index, field)| {
                        *field
                            != (TypeRecipe::ProductParameter {
                                owner: family,
                                index: index as u32,
                            })
                    }) =>
            {
                return None
            }
            _ => {}
        }
        let mut left = 64;
        for field in &fields {
            field_recipe_with_projections(field, family, arity, &mut left,
                &|id| projected.then(|| self.projection_arities.get(&id).copied()).flatten())?;
        }
        if let Some(index) = self.products.families.get(&family) {
            let schema = &self.products.schemas[*index];
            return (schema.arity == arity && schema.fields == fields).then_some(());
        }
        let index = self.products.schemas.len();
        let type_constructor = match family {
            ProductFamily::Enum(_) => return None,
            ProductFamily::Unit => "ty_unit".into(),
            ProductFamily::Tuple(n) => format!("ty_tuple{n}"),
            ProductFamily::Struct(id) => {
                if self
                    .adt_recipes
                    .get(&id)
                    .is_some_and(|old| *old != super::RecipeAdt::Struct(arity))
                {
                    return None;
                }
                self.adt_recipes.insert(id, super::RecipeAdt::Struct(arity));
                let next = u32::try_from(self.opaque_indices.len()).ok()?;
                let nominal = *self.opaque_indices.entry(id).or_insert(next);
                format!("ty_adt{nominal}")
            }
        };
        let types: Vec<_> = (0..arity)
            .flat_map(|_| [Sort::Decoration, Sort::TypeId])
            .collect();
        self.declare_product_function(type_constructor.clone(), types.clone(), Sort::TypeId)?;
        let pack = format!("pack_product{index}");
        let pack_params = types
            .iter()
            .copied()
            .chain(std::iter::repeat_n(Sort::Poly, fields.len()))
            .collect();
        self.declare_product_function(pack.clone(), pack_params, Sort::Poly)?;
        let mut projections = Vec::new();
        for field in 0..fields.len() {
            let name = format!("project_product{index}_{field}");
            self.declare_product_function(
                name.clone(),
                types.iter().copied().chain([Sort::Poly]).collect(),
                Sort::Poly,
            )?;
            self.products
                .operations
                .insert(name.clone(), Operation::Projection(index));
            projections.push(name);
        }
        self.products
            .operations
            .insert(pack.clone(), Operation::Pack(index));
        self.products
            .type_constructors
            .insert(type_constructor.clone(), index);
        self.products.families.insert(family, index);
        self.products.schemas.push(Schema {
            family,
            arity,
            fields,
            pack,
            projections,
            type_constructor,
        });
        Some(())
    }

    pub(crate) fn pack_product(
        &mut self,
        family: ProductFamily,
        args: &[TypeArgument],
        fields: Vec<Term>,
    ) -> Option<Term> {
        let symbols = self.projection_symbols.clone();
        self.pack_product_priced(family, args, fields, false, &mut |term, _| !Self::has_projection_term(term, &symbols))
    }

    pub(crate) fn pack_product_with_work(
        &mut self, family: ProductFamily, args: &[TypeArgument], fields: Vec<Term>,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<Term>> {
        super::super::inline_work::items(work, 1 + fields.len(), span)?;
        let mut failure = None;
        let result = self.pack_product_priced(family, args, fields, true, &mut |term, copies| {
            match super::super::inline_work::term(work, term, copies, span) {
                Ok(()) => true, Err(error) => { failure = Some(error); false }
            }
        });
        match failure { Some(error) => Err(error), None => Ok(result) }
    }

    fn pack_product_priced(
        &mut self, family: ProductFamily, args: &[TypeArgument], fields: Vec<Term>,
        projected: bool, price: &mut dyn FnMut(&Term, usize) -> bool,
    ) -> Option<Term> {
        let schema = self
            .products
            .schemas
            .get(*self.products.families.get(&family)?)?;
        if args.len() != schema.arity
            || fields.len() != schema.fields.len()
            || fields.iter().any(|field| field.sort() != Sort::Poly)
        {
            return None;
        }
        if !projected && schema.fields.iter().any(TypeRecipe::has_projection) { return None; }
        for argument in args { for term in argument.terms_ref() { if !price(term, 1) { return None; } } }
        let name = schema.pack.clone();
        let terms = prefix(args).into_iter().chain(fields).collect();
        Some(self.call(name, terms, Sort::Poly))
    }

    pub(crate) fn project_product(
        &mut self,
        family: ProductFamily,
        args: &[TypeArgument],
        value: Term,
    ) -> Option<Vec<Term>> {
        let symbols = self.projection_symbols.clone();
        self.project_product_priced(family, args, value, false, &mut |term, _| !Self::has_projection_term(term, &symbols))
    }

    pub(crate) fn project_product_with_work(
        &mut self, family: ProductFamily, args: &[TypeArgument], value: Term,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<Vec<Term>>> {
        super::super::inline_work::items(work, 1 + args.len(), span)?;
        let mut failure = None;
        let result = self.project_product_priced(family, args, value, true, &mut |term, copies| {
            match super::super::inline_work::term(work, term, copies, span) {
                Ok(()) => true, Err(error) => { failure = Some(error); false }
            }
        });
        match failure { Some(error) => Err(error), None => Ok(result) }
    }

    fn project_product_priced(
        &mut self, family: ProductFamily, args: &[TypeArgument], value: Term,
        projected: bool, price: &mut dyn FnMut(&Term, usize) -> bool,
    ) -> Option<Vec<Term>> {
        let schema = self
            .products
            .schemas
            .get(*self.products.families.get(&family)?)?;
        if args.len() != schema.arity || value.sort() != Sort::Poly {
            return None;
        }
        if !projected && schema.fields.iter().any(TypeRecipe::has_projection) { return None; }
        for argument in args { for term in argument.terms_ref() { if !price(term, schema.projections.len()) { return None; } } }
        if !price(&value, schema.projections.len()) { return None; }
        let names = schema.projections.clone();
        Some(
            names
                .into_iter()
                .map(|name| {
                    let terms = prefix(args).into_iter().chain([value.clone()]).collect();
                    self.call(name, terms, Sort::Poly)
                })
                .collect(),
        )
    }

    fn product_facts(
        &mut self,
        schema: &Schema,
        terms: &[Term],
        value: Term,
        packed_fields: Option<&[Term]>,
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        let type_size = terms
            .iter()
            .try_fold(0usize, |size, term| size.checked_add(term.size()))?;
        let cost = value
            .size()
            .checked_add(type_size)?
            .checked_add(1)?
            .checked_mul(schema.fields.len().checked_mul(8)?.checked_add(8)?)?;
        *budget = budget.checked_sub(cost)?;
        let args = arguments(terms, schema.arity)?;
        let identity = self.call(
            schema.type_constructor.clone(),
            terms.to_vec(),
            Sort::TypeId,
        );
        let mut field_types = Vec::new();
        for field in &schema.fields {
            let empty = HashMap::new();
            let argument = self.argument_in(field, &TypeEnv::default(), Some((schema.family, &args)),
                &mut |term, copies| (0..copies).all(|_| super::super::substitution::price(term, &empty, budget).is_some()))?;
            field_types.push(self.canonical_argument(argument, budget)?);
        }
        let empty = HashMap::new();
        let projections = self.project_product_priced(schema.family, &args, value.clone(), true,
            &mut |term, copies| (0..copies).all(|_| super::super::substitution::price(term, &empty, budget).is_some()))?;
        let member = self.membership(value.clone(), identity.clone())?;
        let mut facts = Vec::new();
        for (field, ty) in projections.iter().zip(&field_types) {
            let field_member = self.membership(field.clone(), ty.identity().clone())?;
            facts.push(Term::implies(member.clone(), field_member));
        }
        let restored = self.pack_product_priced(schema.family, &args, projections.clone(), true,
            &mut |term, copies| (0..copies).all(|_| super::super::substitution::price(term, &empty, budget).is_some()))?;
        facts.push(Term::implies(member, Term::eq(restored, value.clone())));
        if let Some(fields) = packed_fields {
            if fields.len() != field_types.len()
                || fields.iter().any(|field| field.sort() != Sort::Poly)
            {
                return None;
            }
            let mut typed = Vec::new();
            for (field, ty) in fields.iter().zip(&field_types) {
                typed.push(self.membership(field.clone(), ty.identity().clone())?);
            }
            let guard = Term::and(typed);
            let membership = self.membership(value, identity)?;
            facts.push(Term::implies(guard.clone(), membership));
            for (actual, expected) in projections.into_iter().zip(fields) {
                facts.push(Term::implies(
                    guard.clone(),
                    Term::eq(actual, expected.clone()),
                ));
            }
        }
        facts.retain(|fact| *fact != Term::Bool(true));
        for fact in &facts {
            *budget = budget.checked_sub(fact.size())?;
        }
        Some(facts)
    }

    fn product_bridge_axioms(&mut self, roots: &[&Term], budget: &mut usize) -> Option<Vec<Term>> {
        let mut applications = Vec::new();
        let mut seen = HashSet::new();
        let mut exhausted = false;
        for root in roots {
            *budget = budget.checked_sub(root.size())?;
            root.for_each_typed_call(&mut |name, args, sort| {
                if exhausted || !(name == "has_type" || self.products.operations.contains_key(name))
                {
                    return;
                }
                if self.functions.get(name).is_none_or(|signature| {
                    signature.ret != sort
                        || signature.params.len() != args.len()
                        || signature
                            .params
                            .iter()
                            .zip(args)
                            .any(|(expected, actual)| *expected != actual.sort())
                }) {
                    exhausted = true;
                    return;
                }
                let Some(cost) = args
                    .iter()
                    .try_fold(0usize, |n, arg| n.checked_add(arg.size()))
                    .and_then(|n| n.checked_mul(2))
                else {
                    exhausted = true;
                    return;
                };
                let Some(left) = budget.checked_sub(cost) else {
                    exhausted = true;
                    return;
                };
                *budget = left;
                let row = (name.to_owned(), args.to_vec());
                if seen.insert(row.clone()) {
                    applications.push(row);
                }
            });
        }
        if exhausted {
            return None;
        }
        let mut seeds = HashMap::<(usize, Vec<Term>, Term), Option<Vec<Term>>>::new();
        for (name, args) in applications {
            match self.products.operations.get(&name).copied() {
                Some(Operation::Pack(index)) => {
                    let schema = &self.products.schemas[index];
                    let n = schema.arity.checked_mul(2)?;
                    if args.len() != n.checked_add(schema.fields.len())? {
                        return None;
                    }
                    arguments(&args[..n], schema.arity)?;
                    let value = Term::call(name, args.clone(), Sort::Poly);
                    seeds.insert((index, args[..n].to_vec(), value), Some(args[n..].to_vec()));
                }
                Some(Operation::Projection(index)) => {
                    let schema = &self.products.schemas[index];
                    let n = schema.arity.checked_mul(2)?;
                    if args.len() != n.checked_add(1)? || args[n].sort() != Sort::Poly {
                        return None;
                    }
                    arguments(&args[..n], schema.arity)?;
                    seeds
                        .entry((index, args[..n].to_vec(), args[n].clone()))
                        .or_insert(None);
                }
                None if name == "has_type" => {
                    let [value, identity] = args.as_slice() else {
                        return None;
                    };
                    if value.sort() != Sort::Poly || identity.sort() != Sort::TypeId {
                        return None;
                    }
                    if let Term::Call {
                        name,
                        args,
                        sort: Sort::TypeId,
                    } = identity
                    {
                        if let Some(index) = self.products.type_constructors.get(name).copied() {
                            arguments(args, self.products.schemas[index].arity)?;
                            seeds
                                .entry((index, args.clone(), value.clone()))
                                .or_insert(None);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut seeds: Vec<_> = seeds.into_iter().collect();
        seeds.sort_by_key(|(key, _)| format!("{key:?}"));
        let mut facts = Vec::new();
        for ((index, types, value), fields) in seeds {
            let schema = self.products.schemas[index].clone();
            facts.extend(self.product_facts(&schema, &types, value, fields.as_deref(), budget)?);
        }
        Some(facts)
    }

    pub(crate) fn bridge_axioms(
        &mut self,
        roots: &[&Term],
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        let mut reference_facts = self.mut_ref_bridge_axioms(roots, budget)?;
        let reference_roots: Vec<_> = roots
            .iter()
            .copied()
            .chain(reference_facts.iter())
            .collect();
        let mut sums = self.sum_bridge_axioms(&reference_roots, budget)?;
        sums.append(&mut reference_facts);
        let sum_roots: Vec<_> = roots.iter().copied().chain(sums.iter()).collect();
        let mut products = if self.products.schemas.is_empty() {
            Vec::new()
        } else {
            self.product_bridge_axioms(&sum_roots, budget)?
        };
        products.append(&mut sums);
        let inputs: Vec<_> = roots.iter().copied().chain(products.iter()).collect();
        let scalar = self.scalar_bridge_axioms(&inputs, budget)?;
        products.extend(scalar);
        Some(products)
    }
}

#[cfg(test)]
mod tests;
