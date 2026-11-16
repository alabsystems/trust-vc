// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Structural source identities for evaluated argument value slots.
use super::*;
use std::rc::Rc;

struct Binding<'a> {
    local: LocalId,
    initializer: &'a Expr,
    previous: Option<Rc<Binding<'a>>>,
}

impl Builder<'_, '_> {
    pub(super) fn argument_source(&self, value: &Expr, path: &[Projection]) -> R<Option<Place>> {
        self.charge(path.len())?;
        let mut path = path.to_vec();
        let mut value = value;
        let mut environment: Option<Rc<Binding<'_>>> = None;
        // Each initializer uses the environment before its binding, including
        // when a nested binding reuses a Bound id. The persistent lexical
        // chain is acyclic; following it uses no recursive Rust call stack.
        loop {
            self.charge(1 + path.len())?;
            match &value.kind {
                ExprKind::Read(place) => {
                    self.work.places(std::slice::from_ref(place), value.span)?;
                    self.charge(1)?;
                    let mut scope = environment.clone();
                    let mut found = None;
                    while let Some(binding) = scope {
                        self.charge(1)?;
                        if binding.local == place.local {
                            found = Some(binding);
                            break;
                        }
                        scope = binding.previous.clone();
                    }
                    if let Some(binding) = found {
                        let mut projections = place.projections.clone();
                        projections.extend(path);
                        path = projections;
                        value = binding.initializer;
                        self.charge(1)?;
                        environment = binding.previous.clone();
                        continue;
                    }
                    if self
                        .decl
                        .local(place.local)
                        .is_some_and(|local| local.kind == LocalKind::Bound)
                    {
                        return Ok(None);
                    }
                    let mut source = place.clone();
                    source.projections.extend(path);
                    return Ok(Some(source));
                }
                ExprKind::Tuple(fields) => {
                    let Some(Projection::TupleField(index)) = path.first().copied() else {
                        return Ok(None);
                    };
                    let Some(field) = fields.get(index as usize) else {
                        return Ok(None);
                    };
                    path.remove(0);
                    value = field;
                }
                ExprKind::Ctor {
                    variant, fields, ..
                } => {
                    let Some(Projection::Field {
                        variant: selected,
                        field,
                    }) = path.first().copied()
                    else {
                        return Ok(None);
                    };
                    if selected != *variant {
                        return Ok(None);
                    }
                    let Some(field) = fields.get(field as usize) else {
                        return Ok(None);
                    };
                    path.remove(0);
                    value = field;
                }
                ExprKind::Field {
                    base,
                    variant,
                    field,
                } => {
                    path.insert(
                        0,
                        Projection::Field {
                            variant: *variant,
                            field: *field,
                        },
                    );
                    value = base;
                }
                ExprKind::TupleField { base, index } => {
                    path.insert(0, Projection::TupleField(*index));
                    value = base;
                }
                ExprKind::Let {
                    local,
                    value: initializer,
                    body,
                } => {
                    self.charge(2)?;
                    environment = Some(Rc::new(Binding {
                        local: *local,
                        initializer,
                        previous: environment.clone(),
                    }));
                    value = body;
                }
                ExprKind::MutRefUpdate {
                    reference,
                    value: updated,
                } => {
                    if path.first() == Some(&Projection::Deref) {
                        path.remove(0);
                        value = updated;
                    } else {
                        value = reference;
                    }
                }
                // A nonstructural value has no unique source-place authority.
                // Its moved origins remain unmatched captures below.
                _ => return Ok(None),
            }
        }
    }

    pub(super) fn extra_origins(
        &self,
        state: &OwnershipState,
        value: &Expr,
        selected: &[Place],
    ) -> R<Vec<ExtraOrigin>> {
        let mut sources = Vec::new();
        for event in self.value_moves(value)? {
            if let Event::Move(place) = event {
                let (mut targets, _) =
                    self.possible_targets(&state.aliases, &state.loans, &state.escaped, &place)?;
                self.union(&mut targets, std::slice::from_ref(&place))?;
                for target in targets {
                    for owner in state.loans.keys() {
                        self.charge(
                            (1 + owner.projections.len())
                                .saturating_mul(1 + selected.len())
                                .saturating_add(target.projections.len()),
                        )?;
                        if owner.local == target.local
                            && owner.projections.starts_with(&target.projections)
                            && !selected.contains(owner)
                        {
                            self.union(&mut sources, std::slice::from_ref(owner))?;
                        }
                    }
                }
            }
        }
        let mut extras = Vec::new();
        for source in sources {
            if let Some(loans) = state.loans.get(&source) {
                self.charge(1)?;
                self.work.places(loans, value.span)?;
                extras.push(ExtraOrigin {
                    source,
                    loans: loans.clone(),
                });
            }
        }
        Ok(extras)
    }
}
