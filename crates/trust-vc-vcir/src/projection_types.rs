//! Finite closed implementation semantics, not inferred projection axioms.
//!
//! Normalization is one canonical operation shared by WF, instance matching
//! and type-term encoding. Every owned type copy debits the caller's budget.

use crate::{AdtId, ProjectionDecl, ProjectionId, ProjectionImpl, ProjectionValue, Ty, VcCrate};
use std::collections::{HashMap, HashSet};
mod dependencies;

#[derive(Clone, Default)]
pub(crate) struct Definitions<'a> {
    declarations: HashMap<ProjectionId, &'a ProjectionDecl>,
    implementations: HashMap<ProjectionId, HashMap<Vec<Ty>, &'a ProjectionValue>>,
}

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    match work.checked_sub(amount) {
        Some(left) => { *work = left; Some(()) }
        None => { *work = 0; None }
    }
}

fn closed_canonical(ty: &Ty, adts: &HashMap<AdtId, usize>, work: &mut usize) -> Option<()> {
    let mut pending = vec![(ty, 0usize)];
    while let Some((ty, depth)) = pending.pop() {
        charge(work, 1)?;
        if depth >= 64 { return None; }
        match ty {
            Ty::Bool | Ty::Unit => {}
            Ty::Int(range) if range.is_valid() => {}
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => pending.push((inner, depth + 1)),
            Ty::Tuple(args) if !args.is_empty() => {
                charge(work, args.len())?;
                pending.extend(args.iter().map(|ty| (ty, depth + 1)));
            }
            Ty::Adt(id, args) if adts.get(id) == Some(&args.len()) => {
                charge(work, args.len())?;
                pending.extend(args.iter().map(|ty| (ty, depth + 1)));
            }
            // No open, cyclic, chained or ambiguous RHS normalization. A
            // future producer must normalize nested aliases in the same TcX.
            _ => return None,
        }
    }
    Some(())
}

impl<'a> Definitions<'a> {
    pub(crate) fn checked(source: &'a VcCrate, work: &mut usize) -> Option<Self> {
        if source.projections.is_empty() && source.projection_impls.is_empty() { return Some(Self::default()); }
        charge(work, source.adts.len().checked_add(source.projections.len())?)?;
        let adts: HashMap<_, _> = source.adts.iter().map(|adt| (adt.id, adt.type_params.len())).collect();
        if adts.len() != source.adts.len() { return None; }
        let mut declarations = HashMap::new();
        let mut traits: HashMap<crate::DefHash, (usize, HashSet<ProjectionId>)> = HashMap::new();
        for declaration in &source.projections {
            charge(work, 1)?;
            if declaration.arity == 0 || declarations.insert(declaration.id, declaration).is_some() { return None; }
            let (arity, members) = traits.entry(declaration.trait_id).or_insert_with(|| (declaration.arity, HashSet::new()));
            if *arity != declaration.arity || !members.insert(declaration.id) { return None; }
        }
        let mut identities = HashSet::new();
        let mut definitions = HashSet::new();
        let mut domains: HashMap<crate::DefHash, Vec<&ProjectionImpl>> = HashMap::new();
        let mut implementations: HashMap<ProjectionId, HashMap<Vec<Ty>, &ProjectionValue>> = HashMap::new();
        for implementation in &source.projection_impls {
            charge(work, 1 + implementation.arguments.len() + implementation.values.len())?;
            if !identities.insert(implementation.id) || implementation.arguments.is_empty()
                || implementation.values.is_empty() { return None; }
            let (arity, required_members) = traits.get(&implementation.trait_id)?;
            if *arity != implementation.arguments.len() || required_members.len() != implementation.values.len() { return None; }
            for argument in &implementation.arguments { closed_canonical(argument, &adts, work)?; }
            // A trait/argument domain has exactly one represented selection.
            // Equal RHS values do not excuse conflicting implementation IDs.
            for previous in domains.get(&implementation.trait_id).into_iter().flatten() {
                for argument in &implementation.arguments { closed_canonical(argument, &adts, work)?; }
                for argument in &previous.arguments { closed_canonical(argument, &adts, work)?; }
                if previous.arguments == implementation.arguments { return None; }
            }
            domains.entry(implementation.trait_id).or_default().push(implementation);
            let mut members = HashSet::new();
            for value in &implementation.values {
                charge(work, 1)?;
                let declaration = declarations.get(&value.declaration)?;
                if declaration.trait_id != implementation.trait_id
                    || declaration.arity != implementation.arguments.len()
                    || !members.insert(value.declaration)
                    || !definitions.insert(value.definition) { return None; }
                closed_canonical(&value.ty, &adts, work)?;
                for argument in &implementation.arguments {
                    closed_canonical(argument, &adts, work)?;
                    closed_canonical(argument, &adts, work)?;
                }
                if implementations.entry(value.declaration).or_default()
                    .insert(implementation.arguments.clone(), value).is_some() { return None; }
            }
            charge(work, required_members.len())?;
            if members != *required_members { return None; }
        }
        let definitions = Self { declarations, implementations };
        dependencies::check(&definitions, source, work)?;
        Some(definitions)
    }

    pub(crate) fn lookup(&self, member: ProjectionId, arguments: &[Ty], work: &mut usize) -> Option<Option<&'a Ty>> {
        let declaration = self.declarations.get(&member)?;
        if declaration.arity != arguments.len() { return None; }
        // Price both hash and equality before the exact typed-program lookup.
        for argument in arguments {
            super::instance_semantics::price_type(argument, work)?;
            super::instance_semantics::price_type(argument, work)?;
        }
        Some(self.implementations.get(&member).and_then(|domain| domain.get(arguments)).map(|value| &value.ty))
    }

    pub(crate) fn normalize(&self, ty: &Ty, work: &mut usize) -> Option<Ty> {
        self.normalize_at(ty, None, work, 0)
    }

    pub(crate) fn substitute(&self, ty: &Ty, arguments: &[Ty], work: &mut usize) -> Option<Ty> {
        self.normalize_at(ty, Some(arguments), work, 0)
    }

    /// Raw declaration dependencies must survive until their graph edges
    /// have been collected. This is single-level substitution, not reduction.
    fn raw_substitute(&self, ty: &Ty, arguments: Option<&[Ty]>, work: &mut usize, depth: usize) -> Option<Ty> {
        charge(work, 1)?;
        if depth >= 64 { return None; }
        Some(match ty {
            Ty::Param(index) if arguments.is_some() => self.raw_substitute(arguments?.get(*index as usize)?, None, work, depth + 1)?,
            Ty::Tuple(args) | Ty::Adt(_, args) | Ty::Projection(_, args) => {
                charge(work, args.len())?;
                let args = args.iter().map(|ty| self.raw_substitute(ty, arguments, work, depth + 1)).collect::<Option<Vec<_>>>()?;
                match ty {
                    Ty::Tuple(_) => Ty::Tuple(args),
                    Ty::Adt(id, _) => Ty::Adt(*id, args),
                    Ty::Projection(id, _) => {
                        if self.declarations.get(id)?.arity != args.len() { return None; }
                        Ty::Projection(*id, args)
                    }
                    _ => return None,
                }
            }
            Ty::Ref { mutable, inner } => Ty::Ref { mutable: *mutable, inner: Box::new(self.raw_substitute(inner, arguments, work, depth + 1)?) },
            Ty::MutRef(inner) => Ty::MutRef(Box::new(self.raw_substitute(inner, arguments, work, depth + 1)?)),
            _ => ty.clone(),
        })
    }

    pub(crate) fn is_empty(&self) -> bool { self.implementations.is_empty() }

    pub(crate) fn equal_substitution(&self, formal: &Ty, arguments: Option<&[Ty]>, actual: &Ty, work: &mut usize) -> Option<bool> {
        let expected = self.normalize_at(formal, arguments, work, 0)?;
        let actual = self.normalize(actual, work)?;
        crate::instance_semantics::price_type(&expected, work)?;
        crate::instance_semantics::price_type(&actual, work)?;
        Some(expected == actual)
    }

    fn normalize_at(&self, ty: &Ty, environment: Option<&[Ty]>, work: &mut usize, depth: usize) -> Option<Ty> {
        charge(work, 1)?;
        if depth >= 64 { return None; }
        Some(match ty {
            Ty::Param(index) if environment.is_some() => {
                let argument = environment?.get(*index as usize)?;
                // Caller parameters are not recursively reinterpreted as
                // positions in the callee's argument vector.
                self.normalize_at(argument, None, work, depth + 1)?
            }
            Ty::Tuple(args) | Ty::Adt(_, args) | Ty::Projection(_, args) => {
                charge(work, args.len())?;
                let args = args.iter().map(|ty| self.normalize_at(ty, environment, work, depth + 1)).collect::<Option<Vec<_>>>()?;
                match ty {
                    Ty::Tuple(_) => Ty::Tuple(args),
                    Ty::Adt(id, _) => Ty::Adt(*id, args),
                    Ty::Projection(id, _) => match self.lookup(*id, &args, work)? {
                        Some(result) => self.normalize_at(result, None, work, depth + 1)?,
                        None => Ty::Projection(*id, args),
                    },
                    _ => return None,
                }
            }
            Ty::Ref { mutable, inner } => Ty::Ref { mutable: *mutable, inner: Box::new(self.normalize_at(inner, environment, work, depth + 1)?) },
            Ty::MutRef(inner) => Ty::MutRef(Box::new(self.normalize_at(inner, environment, work, depth + 1)?)),
            _ => ty.clone(),
        })
    }
}

#[cfg(test)]
mod tests;
