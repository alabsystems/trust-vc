// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Declaration identity and definite assignment authenticate ANF transport.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct Produced {
    raw: Mode,
    boundary: Mode,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Origin {
    Absent,
    Declared { site: usize, mode: Option<Produced> },
    Invalid,
}

pub(super) fn merge(a: Origin, b: Origin) -> Origin {
    match (a, b) {
        (Origin::Absent, Origin::Absent) => Origin::Absent,
        (Origin::Declared { site: a, mode: am }, Origin::Declared { site: b, mode: bm })
            if a == b =>
        {
            Origin::Declared {
                site: a,
                mode: am.zip(bm).map(|(a, b)| Produced {
                    raw: join(a.raw, b.raw),
                    boundary: join(a.boundary, b.boundary),
                }),
            }
        }
        _ => Origin::Invalid,
    }
}

enum Frame<'a> {
    Type(&'a Ty, Option<usize>),
    Enter(&'a AdtDecl, usize),
    Exit(AdtId),
}

// Borrowed layout traversal: no substituted type trees or recursive stack.
// Unknown parameters, reference carriers and recursive/opaque layouts cannot
// gain value-mode authority from a generated storage declaration.
fn fixed_nonowned(index: &Index<'_>, ty: &Ty) -> bool {
    let mut pending = vec![Frame::Type(ty, None)];
    let mut active = HashSet::new();
    let mut closed = HashSet::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Type(ty, parameters) => match ty {
                Ty::Bool | Ty::Int(_) | Ty::Unit => {}
                Ty::Param(parameter) => {
                    if parameters.is_none_or(|count| *parameter as usize >= count) {
                        return false;
                    }
                }
                Ty::Ref { .. } | Ty::MutRef(_) | Ty::Projection(..) => return false,
                Ty::Tuple(fields) => {
                    pending.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|field| Frame::Type(field, parameters)),
                    );
                }
                Ty::Adt(id, args) => {
                    let Some(adt) = index.adts.get(id).copied() else {
                        return false;
                    };
                    if args.len() != adt.type_params.len() {
                        return false;
                    }
                    pending.push(Frame::Enter(adt, args.len()));
                    pending.extend(args.iter().rev().map(|arg| Frame::Type(arg, parameters)));
                }
            },
            Frame::Enter(adt, parameters) => {
                // Type arguments have already been checked. Repeated nominal
                // fields need not expand the same closed scalar layout again.
                if closed.contains(&adt.id) {
                    continue;
                }
                if adt.kind != AdtKind::Struct || adt.variants.len() != 1 || !active.insert(adt.id)
                {
                    return false;
                }
                pending.push(Frame::Exit(adt.id));
                pending.extend(
                    adt.variants[0]
                        .fields
                        .iter()
                        .rev()
                        .map(|field| Frame::Type(&field.ty, Some(parameters))),
                );
            }
            Frame::Exit(id) => {
                active.remove(&id);
                closed.insert(id);
            }
        }
    }
    true
}

pub(super) fn eligible(index: &Index<'_>, local: &crate::LocalDecl) -> bool {
    local.kind == LocalKind::Temp
        && (local.ty == Ty::Unit
            || (local.mode == Mode::Spec
                && local.prophecy == crate::DeclProphecy::DelayedInfer
                && fixed_nonowned(index, &local.ty)))
}

pub(super) fn return_matches(formal: &Ty, args: &[Ty], actual: &Ty) -> bool {
    let mut pending = vec![(formal, actual)];
    while let Some((formal, actual)) = pending.pop() {
        match (formal, actual) {
            // Substitution is one level: caller-side Params in an actual
            // argument must not be reinterpreted as callee parameters.
            (Ty::Param(index), _) => {
                if args.get(*index as usize) != Some(actual) {
                    return false;
                }
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                pending.extend(a.iter().zip(b));
            }
            (Ty::Adt(ai, a), Ty::Adt(bi, b)) => {
                if ai != bi || a.len() != b.len() {
                    return false;
                }
                pending.extend(a.iter().zip(b));
            }
            (
                Ty::Ref {
                    mutable: am,
                    inner: a,
                },
                Ty::Ref {
                    mutable: bm,
                    inner: b,
                },
            ) => {
                if am != bm {
                    return false;
                }
                pending.push((a, b));
            }
            (Ty::MutRef(a), Ty::MutRef(b)) => pending.push((a, b)),
            (Ty::Unit | Ty::Bool | Ty::Int(_), _) if formal == actual => {}
            _ => return false,
        }
    }
    true
}

impl Walk<'_, '_> {
    pub(super) fn transport_temp(&self, local: LocalId) -> bool {
        self.eligible.get(local.index()).copied().unwrap_or(false)
    }
    pub(super) fn producer_expected(&self, local: LocalId) -> Mode {
        let Some(decl) = self.decl.local(local) else {
            return Mode::Spec;
        };
        if self.transport_temp(local) && decl.ty != Ty::Unit {
            self.ambient
        } else {
            decl.mode
        }
    }
    pub(super) fn producer_mode(&mut self, local: LocalId, value: &Expr) -> Mode {
        let expected = self.producer_expected(local);
        if self.transport_temp(local) {
            // The storage may hold either an ordinary or a Spec producer.
            // Its eventual consumer, not this ANF save, checks that mode.
            self.expression(value, expected)
        } else {
            self.value_has_mode(value, expected)
        }
    }
    pub(super) fn save_origin(&mut self, local: LocalId, mode: Mode, ty: &Ty) {
        if !self.transport_temp(local) {
            return;
        }
        let typed = self.decl.local(local).is_some_and(|decl| decl.ty == *ty);
        // Literal arms can have raw Exec mode even in a Ghost block. They
        // still cannot export executable values across that erased boundary.
        // Unit retains its separate original raw-value/consumption policy.
        let boundary = if *ty == Ty::Unit {
            Mode::Exec
        } else {
            self.ambient
        };
        if let Some(slot) = self.origins.get_mut(local.index()) {
            *slot = match *slot {
                Origin::Declared { site, mode: None } if typed => Origin::Declared {
                    site,
                    mode: Some(Produced {
                        raw: mode,
                        boundary,
                    }),
                },
                _ => Origin::Invalid,
            };
        }
    }
    pub(super) fn read_origin(&self, place: &Place) -> Option<Mode> {
        if !place.projections.is_empty() || !self.transport_temp(place.local) {
            return None;
        }
        match self.origins.get(place.local.index())? {
            Origin::Declared {
                mode: Some(mode), ..
            } => Some(join(mode.raw, mode.boundary)),
            _ => None,
        }
    }
}
