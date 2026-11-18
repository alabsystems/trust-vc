//! Structural Copy typing under one function's explicit premises.
//!
//! A premise is a typing assumption, never a value, resolution fact or native
//! ownership token. Calls must discharge it in the caller's context. All work
//! can debit the caller's existing ledger; substitution borrows type recipes.

use std::collections::HashMap;

use crate::{AdtDecl, AdtId, AdtKind, ProjectionId, Ty};

/// One shared typing allowance per WF function, not a grant per call/premise.
pub(crate) const WF_WORK: usize = 200_000;

/// Check the entire syntactic type, including unused nominal arguments and
/// reference referents, before interpreting a declaration premise.
pub(crate) fn wellformed_with<E>(
    adts: &HashMap<AdtId, &AdtDecl>,
    projections: &impl Fn(ProjectionId) -> Option<usize>,
    ty: &Ty,
    parameters: usize,
    mut charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    charge(1)?;
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        charge(1)?;
        match ty {
            Ty::Bool | Ty::Unit => {}
            Ty::Int(range) if range.is_valid() => {}
            Ty::Int(_) => return Ok(false),
            Ty::Param(index) if (*index as usize) < parameters => {}
            Ty::Param(_) => return Ok(false),
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => {
                charge(1)?;
                pending.push(inner);
            }
            Ty::Tuple(fields) => {
                if fields.is_empty() {
                    return Ok(false);
                }
                charge(fields.len())?;
                pending.extend(fields);
            }
            Ty::Adt(id, arguments) => {
                let Some(declaration) = adts.get(id) else {
                    return Ok(false);
                };
                if declaration.type_params.len() != arguments.len() {
                    return Ok(false);
                }
                charge(arguments.len())?;
                pending.extend(arguments);
            }
            Ty::Projection(id, arguments) => {
                if arguments.is_empty() || projections(*id) != Some(arguments.len()) {
                    return Ok(false);
                }
                charge(arguments.len())?;
                pending.extend(arguments);
            }
        }
    }
    Ok(true)
}

#[derive(Clone, Copy)]
struct View<'a> {
    ty: &'a Ty,
    environment: Option<usize>,
    ancestors: Option<usize>,
}

struct Ancestor {
    datatype: AdtId,
    parent: Option<usize>,
}

struct Walk<'a, F> {
    environments: Vec<Vec<View<'a>>>,
    ancestors: Vec<Ancestor>,
    charge: F,
}

impl<'a, E, F: FnMut(usize) -> Result<(), E>> Walk<'a, F> {
    fn root(&mut self, ty: &'a Ty, arguments: Option<&'a [Ty]>) -> Result<View<'a>, E> {
        let environment = if let Some(arguments) = arguments {
            (self.charge)(1 + arguments.len())?;
            let index = self.environments.len();
            self.environments.push(
                arguments
                    .iter()
                    .map(|ty| View {
                        ty,
                        environment: None,
                        ancestors: None,
                    })
                    .collect(),
            );
            Some(index)
        } else {
            None
        };
        Ok(View {
            ty,
            environment,
            ancestors: None,
        })
    }

    fn resolve(&mut self, mut view: View<'a>) -> Result<Option<View<'a>>, E> {
        loop {
            (self.charge)(1)?;
            let (Ty::Param(index), Some(environment)) = (view.ty, view.environment) else {
                return Ok(Some(view));
            };
            let Some(argument) = self
                .environments
                .get(environment)
                .and_then(|args| args.get(*index as usize))
            else {
                return Ok(None);
            };
            // Arguments retain their outer environment; a caller's parameter
            // is never recursively reinterpreted as this callee's index.
            view = *argument;
        }
    }

    fn equal(&mut self, left: View<'a>, right: View<'a>) -> Result<bool, E> {
        (self.charge)(1)?;
        let mut pending = vec![(left, right)];
        while let Some((left, right)) = pending.pop() {
            let (Some(left), Some(right)) = (self.resolve(left)?, self.resolve(right)?) else {
                return Ok(false);
            };
            let fields = match (left.ty, right.ty) {
                (Ty::Bool, Ty::Bool) | (Ty::Unit, Ty::Unit) => continue,
                (Ty::Int(a), Ty::Int(b)) if a == b => continue,
                (Ty::Param(a), Ty::Param(b)) if a == b => continue,
                (Ty::Tuple(a), Ty::Tuple(b)) => Some((a.as_slice(), b.as_slice())),
                (Ty::Adt(a, x), Ty::Adt(b, y)) if a == b => Some((x.as_slice(), y.as_slice())),
                (Ty::Projection(a, x), Ty::Projection(b, y)) if a == b => Some((x.as_slice(), y.as_slice())),
                (
                    Ty::Ref {
                        mutable: a,
                        inner: x,
                    },
                    Ty::Ref {
                        mutable: b,
                        inner: y,
                    },
                ) if a == b => {
                    (self.charge)(1)?;
                    pending.push((View { ty: x, ..left }, View { ty: y, ..right }));
                    continue;
                }
                (Ty::MutRef(x), Ty::MutRef(y)) => {
                    (self.charge)(1)?;
                    pending.push((View { ty: x, ..left }, View { ty: y, ..right }));
                    continue;
                }
                _ => return Ok(false),
            };
            if let Some((a, b)) = fields {
                if a.len() != b.len() {
                    return Ok(false);
                }
                (self.charge)(a.len())?;
                pending.extend(
                    a.iter()
                        .zip(b)
                        .map(|(a, b)| (View { ty: a, ..left }, View { ty: b, ..right })),
                );
            }
        }
        Ok(true)
    }

    fn check(
        &mut self,
        adts: &'a HashMap<AdtId, &'a AdtDecl>,
        premises: &'a [Ty],
        root: View<'a>,
        possible: bool,
    ) -> Result<bool, E> {
        (self.charge)(1)?;
        let mut pending = vec![root];
        let mut seen = Vec::new();
        while let Some(view) = pending.pop() {
            let Some(view) = self.resolve(view)? else {
                return Ok(false);
            };
            match view.ty {
                Ty::Bool | Ty::Unit => continue,
                Ty::Int(range) if range.is_valid() => continue,
                Ty::Ref { mutable: false, .. } => continue,
                Ty::MutRef(_) | Ty::Ref { mutable: true, .. } | Ty::Int(_) => return Ok(false),
                Ty::Adt(id, arguments) => {
                    let Some(decl) = adts.get(id) else {
                        return Ok(false);
                    };
                    if decl.kind == AdtKind::Opaque || decl.type_params.len() != arguments.len() {
                        return Ok(false);
                    }
                    let mut ancestor = view.ancestors;
                    while let Some(index) = ancestor {
                        (self.charge)(1)?;
                        let entry = &self.ancestors[index];
                        if entry.datatype == *id {
                            return Ok(false);
                        }
                        ancestor = entry.parent;
                    }
                }
                _ => {}
            }
            // Borrowed, fully expanded type equality is prepaid. No recursive
            // type hash, clone, census or unbounded substitution precedes it.
            let mut repeated = false;
            for old in &seen {
                if self.equal(view, *old)? {
                    repeated = true;
                    break;
                }
            }
            if repeated {
                continue;
            }
            (self.charge)(1)?;
            seen.push(view);
            if !possible {
                let mut assumed = false;
                for premise in premises {
                    (self.charge)(1)?;
                    if self.equal(
                        view,
                        View {
                            ty: premise,
                            environment: None,
                            ancestors: None,
                        },
                    )? {
                        assumed = true;
                        break;
                    }
                }
                if assumed {
                    continue;
                }
            }
            match view.ty {
                // An associated type can be Copy only under an exact checked
                // premise. Its constructor supplies no structural Copy rule.
                Ty::Param(_) | Ty::Projection(..) if possible => {}
                Ty::Param(_) | Ty::Projection(..) => return Ok(false),
                Ty::Tuple(fields) => {
                    if fields.is_empty() {
                        return Ok(false);
                    }
                    (self.charge)(fields.len())?;
                    pending.extend(fields.iter().map(|ty| View { ty, ..view }));
                }
                Ty::Adt(id, arguments) => {
                    let declaration = adts[id];
                    if declaration.kind == AdtKind::Struct && declaration.variants.len() != 1 {
                        return Ok(false);
                    }
                    (self.charge)(2 + arguments.len())?;
                    let environment = self.environments.len();
                    // Restore the argument's original layout ancestry when a
                    // formal is resolved. Wrap<Wrap<u8>> is finite, whereas an
                    // actual recursive field layout must not be called Copy.
                    self.environments
                        .push(arguments.iter().map(|ty| View { ty, ..view }).collect());
                    let ancestors = self.ancestors.len();
                    self.ancestors.push(Ancestor {
                        datatype: *id,
                        parent: view.ancestors,
                    });
                    for variant in &declaration.variants {
                        (self.charge)(1 + variant.fields.len())?;
                        pending.extend(variant.fields.iter().map(|field| View {
                            ty: &field.ty,
                            environment: Some(environment),
                            ancestors: Some(ancestors),
                        }));
                    }
                }
                _ => unreachable!("primitive Copy cases were handled above"),
            }
        }
        Ok(true)
    }
}

/// A premise cannot assert Copy for a rigid mutable reference, unknown or
/// opaque layout. Abstract parameters remain possible until call discharge.
pub(crate) fn admissible_with<'a, E>(
    adts: &'a HashMap<AdtId, &'a AdtDecl>,
    ty: &'a Ty,
    charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let mut walk = Walk {
        environments: Vec::new(),
        ancestors: Vec::new(),
        charge,
    };
    let root = walk.root(ty, None)?;
    walk.check(adts, &[], root, true)
}

pub(crate) fn is_copy_with<'a, E>(
    adts: &'a HashMap<AdtId, &'a AdtDecl>,
    premises: &'a [Ty],
    ty: &'a Ty,
    arguments: Option<&'a [Ty]>,
    charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let mut walk = Walk {
        environments: Vec::new(),
        ancestors: Vec::new(),
        charge,
    };
    let root = walk.root(ty, arguments)?;
    if !walk.check(adts, &[], root, true)? {
        return Ok(false);
    }
    walk.check(adts, premises, root, false)
}

pub(crate) fn matches_substitution_with<'a, E>(
    formal: &'a Ty,
    arguments: &'a [Ty],
    actual: &'a Ty,
    charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let mut walk = Walk {
        environments: Vec::new(),
        ancestors: Vec::new(),
        charge,
    };
    let left = walk.root(formal, Some(arguments))?;
    let right = walk.root(actual, None)?;
    walk.equal(left, right)
}

#[cfg(test)]
#[path = "copy_context/tests.rs"]
mod tests;
