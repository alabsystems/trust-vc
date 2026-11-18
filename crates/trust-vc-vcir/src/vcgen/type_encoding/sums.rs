//! Typed ground instances for finite nonrecursive enum values.
//!
//! Every operation retains its declaration family and complete type vector.
//! A selector outside its own variant is unspecified; recommends are not
//! premises and do not restrict the meaning of a nonrecursive spec body.

use std::collections::{HashMap, HashSet};
use std::ops::Not;

use super::{ProductFamily, RecipeAdt, Sort, Term, TypeArgument, TypeEnv, TypeRecipe, Vocabulary};

#[derive(Clone)]
struct Schema {
    family: ProductFamily,
    arity: usize,
    variants: Vec<Vec<TypeRecipe>>,
    type_constructor: String,
    constructors: Vec<String>,
    tests: Vec<String>,
    raw: Vec<Vec<String>>,
    wrapped: Vec<Vec<String>>,
}

#[derive(Clone, Copy)]
enum Operation {
    Constructor(usize, usize),
    View(usize),
}

#[derive(Default)]
pub(super) struct Sums {
    schemas: Vec<Schema>,
    families: HashMap<crate::AdtId, usize>,
    operations: HashMap<String, Operation>,
    type_constructors: HashMap<String, usize>,
}

fn prefix(args: &[TypeArgument]) -> Vec<Term> {
    args.iter().flat_map(TypeArgument::terms).collect()
}

impl Vocabulary {
    pub(crate) fn register_sum(
        &mut self,
        id: crate::AdtId,
        arity: usize,
        variants: Vec<Vec<TypeRecipe>>,
    ) -> Option<()> {
        self.register_sum_inner(id, arity, variants, false)
    }

    pub(crate) fn register_sum_with_work(
        &mut self, id: crate::AdtId, arity: usize, variants: Vec<Vec<TypeRecipe>>,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<()>> {
        super::super::inline_work::items(work, 1 + variants.len(), span)?;
        for fields in &variants {
            super::super::inline_work::items(work, fields.len(), span)?;
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
        }
        Ok(self.register_sum_inner(id, arity, variants, true))
    }

    fn register_sum_inner(
        &mut self, id: crate::AdtId, arity: usize, variants: Vec<Vec<TypeRecipe>>, projected: bool,
    ) -> Option<()> {
        if arity > 64 || variants.is_empty() || variants.len() > 64 {
            return None;
        }
        let family = ProductFamily::Enum(id);
        let mut left = 64usize;
        for fields in &variants {
            left = left.checked_sub(1)?;
            for field in fields {
                super::products::field_recipe_with_projections(field, family, arity, &mut left,
                    &|id| projected.then(|| self.projection_arities.get(&id).copied()).flatten())?;
            }
        }
        if let Some(index) = self.sums.families.get(&id) {
            let schema = &self.sums.schemas[*index];
            return (schema.arity == arity && schema.variants == variants).then_some(());
        }
        if self
            .adt_recipes
            .get(&id)
            .is_some_and(|old| *old != RecipeAdt::Enum(arity))
        {
            return None;
        }
        self.adt_recipes.insert(id, RecipeAdt::Enum(arity));
        let next = u32::try_from(self.opaque_indices.len()).ok()?;
        let nominal = *self.opaque_indices.entry(id).or_insert(next);
        let type_constructor = format!("ty_adt{nominal}");
        let types: Vec<_> = (0..arity)
            .flat_map(|_| [Sort::Decoration, Sort::TypeId])
            .collect();
        self.declare_product_function(type_constructor.clone(), types.clone(), Sort::TypeId)?;
        let index = self.sums.schemas.len();
        let mut constructors = Vec::new();
        let mut tests = Vec::new();
        let mut raw = Vec::new();
        let mut wrapped = Vec::new();
        for (variant, fields) in variants.iter().enumerate() {
            let ctor = format!("sum{index}_ctor{variant}");
            self.declare_product_function(
                ctor.clone(),
                types
                    .iter()
                    .copied()
                    .chain(std::iter::repeat_n(Sort::Poly, fields.len()))
                    .collect(),
                Sort::Poly,
            )?;
            self.sums
                .operations
                .insert(ctor.clone(), Operation::Constructor(index, variant));
            constructors.push(ctor);
            let test = format!("sum{index}_is{variant}");
            let view_params: Vec<_> = types.iter().copied().chain([Sort::Poly]).collect();
            self.declare_product_function(test.clone(), view_params.clone(), Sort::Bool)?;
            self.sums
                .operations
                .insert(test.clone(), Operation::View(index));
            tests.push(test);
            let mut raw_fields = Vec::new();
            let mut wrapped_fields = Vec::new();
            for field in 0..fields.len() {
                let raw_name = format!("sum{index}_raw{variant}_{field}");
                let wrapped_name = format!("sum{index}_field{variant}_{field}");
                for name in [&raw_name, &wrapped_name] {
                    self.declare_product_function(name.clone(), view_params.clone(), Sort::Poly)?;
                    self.sums
                        .operations
                        .insert(name.clone(), Operation::View(index));
                }
                raw_fields.push(raw_name);
                wrapped_fields.push(wrapped_name);
            }
            raw.push(raw_fields);
            wrapped.push(wrapped_fields);
        }
        self.sums
            .type_constructors
            .insert(type_constructor.clone(), index);
        self.sums.families.insert(id, index);
        self.sums.schemas.push(Schema {
            family,
            arity,
            variants,
            type_constructor,
            constructors,
            tests,
            raw,
            wrapped,
        });
        Some(())
    }

    pub(crate) fn construct_sum(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        fields: Vec<Term>,
    ) -> Option<Term> {
        self.construct_sum_inner(id, args, variant, fields, false)
    }

    pub(crate) fn construct_sum_with_work(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        fields: Vec<Term>,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<Term>> {
        super::super::inline_work::items(work, 1 + fields.len(), span)?;
        for argument in args { for term in argument.terms_ref() {
            super::super::inline_work::term(work, term, 1, span)?;
        } }
        Ok(self.construct_sum_inner(id, args, variant, fields, true))
    }

    fn construct_sum_inner(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        fields: Vec<Term>,
        projected: bool,
    ) -> Option<Term> {
        let schema = self.sums.schemas.get(*self.sums.families.get(&id)?)?;
        if !projected && (schema.variants.iter().flatten().any(TypeRecipe::has_projection)
            || args.iter().any(|arg| arg.terms_ref().iter().any(|term| Self::has_projection_term(term, &self.projection_symbols)))) {
            return None;
        }
        let variant = variant as usize;
        if args.len() != schema.arity
            || fields.len() != schema.variants.get(variant)?.len()
            || fields.iter().any(|field| field.sort() != Sort::Poly)
        {
            return None;
        }
        let name = schema.constructors.get(variant)?.clone();
        Some(self.call(
            name,
            prefix(args).into_iter().chain(fields).collect(),
            Sort::Poly,
        ))
    }

    pub(crate) fn test_sum(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        value: Term,
    ) -> Option<Term> {
        self.test_sum_inner(id, args, variant, value, false)
    }

    pub(crate) fn test_sum_with_work(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        value: Term,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<Term>> {
        super::super::inline_work::items(work, 1, span)?;
        for argument in args { for term in argument.terms_ref() {
            super::super::inline_work::term(work, term, 1, span)?;
        } }
        super::super::inline_work::term(work, &value, 1, span)?;
        Ok(self.test_sum_inner(id, args, variant, value, true))
    }

    fn test_sum_inner(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        value: Term,
        projected: bool,
    ) -> Option<Term> {
        let schema = self.sums.schemas.get(*self.sums.families.get(&id)?)?;
        if !projected && (schema.variants.iter().flatten().any(TypeRecipe::has_projection)
            || args.iter().any(|arg| arg.terms_ref().iter().any(|term| Self::has_projection_term(term, &self.projection_symbols)))) {
            return None;
        }
        if args.len() != schema.arity || value.sort() != Sort::Poly {
            return None;
        }
        let name = schema.tests.get(variant as usize)?.clone();
        Some(self.call(
            name,
            prefix(args).into_iter().chain([value]).collect(),
            Sort::Bool,
        ))
    }

    pub(crate) fn project_sum(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        field: u32,
        value: Term,
    ) -> Option<Term> {
        self.project_sum_inner(id, args, variant, field, value, false)
    }

    pub(crate) fn project_sum_with_work(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        field: u32,
        value: Term,
        work: &std::cell::Cell<usize>, span: crate::SpanId,
    ) -> super::super::expr::R<Option<Term>> {
        super::super::inline_work::items(work, 1, span)?;
        for argument in args { for term in argument.terms_ref() {
            super::super::inline_work::term(work, term, 1, span)?;
        } }
        super::super::inline_work::term(work, &value, 1, span)?;
        Ok(self.project_sum_inner(id, args, variant, field, value, true))
    }

    fn project_sum_inner(
        &mut self,
        id: crate::AdtId,
        args: &[TypeArgument],
        variant: u32,
        field: u32,
        value: Term,
        projected: bool,
    ) -> Option<Term> {
        let schema = self.sums.schemas.get(*self.sums.families.get(&id)?)?;
        if !projected && (schema.variants.iter().flatten().any(TypeRecipe::has_projection)
            || args.iter().any(|arg| arg.terms_ref().iter().any(|term| Self::has_projection_term(term, &self.projection_symbols)))) {
            return None;
        }
        if args.len() != schema.arity || value.sort() != Sort::Poly {
            return None;
        }
        let name = schema
            .wrapped
            .get(variant as usize)?
            .get(field as usize)?
            .clone();
        Some(self.call(
            name,
            prefix(args).into_iter().chain([value]).collect(),
            Sort::Poly,
        ))
    }

    fn sum_facts(
        &mut self,
        schema: &Schema,
        types: &[Term],
        value: Term,
        packed: Option<(usize, Vec<Term>)>,
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        let work = schema
            .variants
            .iter()
            .try_fold(schema.variants.len(), |n, fields| {
                n.checked_add(fields.len())
            })?;
        let size = types
            .iter()
            .try_fold(value.size().checked_add(1)?, |n, term| {
                n.checked_add(term.size())
            })?;
        *budget = budget.checked_sub(size.checked_mul(work.checked_mul(16)?.checked_add(16)?)?)?;
        let args = super::products::arguments(types, schema.arity)?;
        let identity = self.call(
            schema.type_constructor.clone(),
            types.to_vec(),
            Sort::TypeId,
        );
        let member = self.membership(value.clone(), identity.clone())?;
        let tags: Vec<_> = schema
            .tests
            .iter()
            .map(|name| {
                self.call(
                    name.clone(),
                    types.iter().cloned().chain([value.clone()]).collect(),
                    Sort::Bool,
                )
            })
            .collect();
        let mut facts = vec![Term::implies(member.clone(), Term::or(tags.clone()))];
        for (i, tag) in tags.iter().enumerate() {
            for other in tags.iter().skip(i + 1) {
                facts.push(Term::implies(
                    member.clone(),
                    Term::and([tag.clone(), other.clone()]).not(),
                ));
            }
        }
        for (variant, fields) in schema.variants.iter().enumerate() {
            let mut raw = Vec::new();
            let mut wrapped = Vec::new();
            let mut field_types = Vec::new();
            let matching = Term::and([member.clone(), tags[variant].clone()]);
            for (field, recipe) in fields.iter().enumerate() {
                let empty = HashMap::new();
                let argument = self.argument_in(recipe, &TypeEnv::default(), Some((schema.family, &args)),
                    &mut |term, copies| (0..copies).all(|_| super::super::substitution::price(term, &empty, budget).is_some()))?;
                let ty = self.canonical_argument(argument, budget)?;
                let raw_value = self.call(
                    schema.raw[variant][field].clone(),
                    types.iter().cloned().chain([value.clone()]).collect(),
                    Sort::Poly,
                );
                let wrapped_value = self.call(
                    schema.wrapped[variant][field].clone(),
                    types.iter().cloned().chain([value.clone()]).collect(),
                    Sort::Poly,
                );
                let typed = self.membership(wrapped_value.clone(), ty.identity().clone())?;
                facts.push(Term::implies(member.clone(), typed));
                facts.push(Term::implies(
                    matching.clone(),
                    Term::eq(wrapped_value.clone(), raw_value.clone()),
                ));
                raw.push(raw_value);
                wrapped.push(wrapped_value);
                field_types.push(ty);
            }
            let restored = self.call(
                schema.constructors[variant].clone(),
                types.iter().cloned().chain(raw.clone()).collect(),
                Sort::Poly,
            );
            facts.push(Term::implies(matching, Term::eq(restored, value.clone())));
            if let Some((actual, actual_fields)) = &packed {
                if *actual != variant {
                    continue;
                }
                if actual_fields.len() != fields.len() {
                    return None;
                }
                let mut typed = Vec::new();
                for (field, ty) in actual_fields.iter().zip(&field_types) {
                    typed.push(self.membership(field.clone(), ty.identity().clone())?);
                }
                let guard = Term::and(typed);
                facts.push(Term::implies(guard.clone(), member.clone()));
                for (index, tag) in tags.iter().enumerate() {
                    let test = if index == variant {
                        tag.clone()
                    } else {
                        tag.clone().not()
                    };
                    facts.push(Term::implies(guard.clone(), test));
                }
                for ((raw, wrapped), actual) in raw.iter().zip(&wrapped).zip(actual_fields) {
                    facts.push(Term::implies(
                        guard.clone(),
                        Term::eq(raw.clone(), actual.clone()),
                    ));
                    facts.push(Term::implies(
                        guard.clone(),
                        Term::eq(wrapped.clone(), actual.clone()),
                    ));
                }
            }
        }
        facts.retain(|fact| *fact != Term::Bool(true));
        for fact in &facts {
            *budget = budget.checked_sub(fact.size())?;
        }
        Some(facts)
    }

    pub(super) fn sum_bridge_axioms(
        &mut self,
        roots: &[&Term],
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        if self.sums.schemas.is_empty() {
            return Some(Vec::new());
        }
        let mut applications = Vec::new();
        let mut seen = HashSet::new();
        let mut invalid = false;
        for root in roots {
            *budget = budget.checked_sub(root.size())?;
            root.for_each_typed_call(&mut |name, args, sort| {
                if invalid || !(name == "has_type" || self.sums.operations.contains_key(name)) {
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
                    invalid = true;
                    return;
                }
                let Some(cost) = args
                    .iter()
                    .try_fold(1usize, |n, arg| n.checked_add(arg.size()))
                    .and_then(|n| n.checked_mul(2))
                else {
                    invalid = true;
                    return;
                };
                let Some(left) = budget.checked_sub(cost) else {
                    invalid = true;
                    return;
                };
                *budget = left;
                let row = (name.to_owned(), args.to_vec());
                if seen.insert(row.clone()) {
                    applications.push(row);
                }
            });
        }
        if invalid {
            return None;
        }
        let mut seeds = HashMap::<(usize, Vec<Term>, Term), Option<(usize, Vec<Term>)>>::new();
        for (name, args) in applications {
            match self.sums.operations.get(&name).copied() {
                Some(operation) => {
                    let (Operation::Constructor(index, _) | Operation::View(index)) = operation;
                    let schema = &self.sums.schemas[index];
                    let n = schema.arity.checked_mul(2)?;
                    let prefix = args.get(..n)?;
                    super::products::arguments(prefix, schema.arity)?;
                    match operation {
                        Operation::Constructor(_, variant) => {
                            if args.len() != n.checked_add(schema.variants[variant].len())? {
                                return None;
                            }
                            let value = Term::call(name, args.clone(), Sort::Poly);
                            seeds.insert(
                                (index, prefix.to_vec(), value),
                                Some((variant, args[n..].to_vec())),
                            );
                        }
                        Operation::View(_) => {
                            if args.len() != n.checked_add(1)? {
                                return None;
                            }
                            seeds
                                .entry((index, prefix.to_vec(), args[n].clone()))
                                .or_insert(None);
                        }
                    }
                }
                None if name == "has_type" => {
                    let [value, Term::Call {
                        name,
                        args,
                        sort: Sort::TypeId,
                    }] = args.as_slice()
                    else {
                        continue;
                    };
                    if let Some(index) = self.sums.type_constructors.get(name).copied() {
                        super::products::arguments(args, self.sums.schemas[index].arity)?;
                        seeds
                            .entry((index, args.clone(), value.clone()))
                            .or_insert(None);
                    }
                }
                _ => {}
            }
        }
        let mut seeds: Vec<_> = seeds.into_iter().collect();
        seeds.sort_by_key(|(key, _)| format!("{key:?}"));
        let mut facts = Vec::new();
        for ((index, types, value), packed) in seeds {
            let schema = self.sums.schemas[index].clone();
            facts.extend(self.sum_facts(&schema, &types, value, packed, budget)?);
        }
        Some(facts)
    }
}

#[cfg(test)]
mod tests;
