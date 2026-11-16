// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Storage authority is derived from types and declarations, not a carrier's
//! mode alone. Callers performing charged ownership analysis price the path
//! and its type substitutions before requesting this borrowed lookup.
use crate::{AdtDecl, AdtId, FnDecl, Mode, Place, Projection, Ty};
use std::collections::HashMap;

pub(crate) const fn join(a: Mode, b: Mode) -> Mode {
    match (a, b) {
        (Mode::Spec, _) | (_, Mode::Spec) => Mode::Spec,
        (Mode::Proof, _) | (_, Mode::Proof) => Mode::Proof,
        _ => Mode::Exec,
    }
}

pub(crate) const fn allows(actual: Mode, expected: Mode) -> bool {
    match expected {
        Mode::Spec => true,
        Mode::Proof => !matches!(actual, Mode::Spec),
        Mode::Exec => matches!(actual, Mode::Exec),
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct PlaceMode {
    pub(crate) mode: Mode,
    /// Every carrier/prefix was executable. Dereferencing a Proof carrier
    /// yields an Exec pointee without making that carrier usable in Exec.
    pub(crate) exec_accessible: bool,
    /// This remains true even when more projections follow the dereference.
    pub(crate) through_spec_mut_ref: bool,
}

pub(crate) fn place_mode(
    decl: &FnDecl,
    adts: &HashMap<AdtId, &AdtDecl>,
    place: &Place,
) -> Option<PlaceMode> {
    let root = decl.local(place.local)?;
    let mut ty = root.ty.clone();
    let mut result = PlaceMode {
        mode: root.mode,
        exec_accessible: root.mode == Mode::Exec,
        through_spec_mut_ref: false,
    };
    for projection in &place.projections {
        ty = match (projection, ty) {
            (Projection::Deref, Ty::MutRef(inner)) => {
                if result.mode == Mode::Spec {
                    result.through_spec_mut_ref = true;
                } else {
                    result.mode = Mode::Exec;
                }
                *inner
            }
            // Shared and pre-new-mut-ref carriers keep their established
            // transparent mode policy. Their writeability is checked in WF.
            (Projection::Deref, Ty::Ref { inner, .. }) => *inner,
            (Projection::TupleField(index), Ty::Tuple(fields)) => {
                fields.get(*index as usize)?.clone()
            }
            (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                let field = adts
                    .get(&id)?
                    .variants
                    .get(*variant as usize)?
                    .fields
                    .get(*field as usize)?;
                result.mode = join(result.mode, field.mode);
                field.ty.subst(&args)
            }
            _ => return None,
        };
        result.exec_accessible &= result.mode == Mode::Exec;
    }
    Some(result)
}
