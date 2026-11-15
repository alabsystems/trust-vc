//! Lower a licensed signature using current-context scalar meanings.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::{AdtId, IntRange, Ty};

use super::*;

pub(super) struct Types<'a, 'library, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) meanings: &'a meaning::MatchedBindings<'library, 'tcx>,
    /// Keys are from the actual selected Erase artifact, never the Keep view.
    pub(super) nominals: &'a BTreeMap<NativeKey, (AdtId, usize)>,
    pub(super) parameters: &'a [u32],
}

impl Types<'_, '_, '_> {
    pub(super) fn lower(&self, value: &alignment::DeclarationType) -> Result<Ty, String> {
        self.at_depth(value, 0)
    }

    fn at_depth(&self, value: &alignment::DeclarationType, depth: usize) -> Result<Ty, String> {
        use alignment::{DeclarationType as D, IntegerWidth};
        if depth > 64 {
            return Err("the imported signature exceeds the type-depth bound".into());
        }
        Ok(match value {
            D::Bool => Ty::Bool,
            D::Integer {
                signed,
                width: IntegerWidth::Fixed(width),
            } => {
                let width = u32::from(*width);
                let range = if *signed {
                    IntRange::I(width)
                } else {
                    IntRange::U(width)
                };
                if !range.is_valid() {
                    return Err("the native integer width is unsupported".into());
                }
                Ty::Int(range)
            }
            D::Integer {
                width: IntegerWidth::Pointer,
                ..
            } => {
                // Native target equality is necessary but does not supply
                // Verus's independent 32/64-bit architecture rule.
                return Err(
                    "pointer-width signature types still require architecture semantics".into(),
                );
            }
            D::Parameter(index) => {
                if self.parameters.get(*index as usize) != Some(index) {
                    return Err(
                        "the signature refers to an unlicensed native parameter index".into(),
                    );
                }
                Ty::Param(*index)
            }
            D::Tuple(elements) if elements.is_empty() => Ty::Unit,
            D::Tuple(elements) if elements.len() >= 2 => Ty::Tuple(
                elements
                    .iter()
                    .map(|element| self.at_depth(element, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            D::Tuple(_) => return Err("one-element tuple signatures are not represented".into()),
            D::LocalNominal {
                declaration,
                arguments,
            } => {
                let (id, arity) = self
                    .nominals
                    .get(declaration)
                    .ok_or("a signature nominal lacks a sealed declaration capability")?;
                if arguments.len() != *arity {
                    return Err("the signature nominal has incomplete type arguments".into());
                }
                Ty::Adt(
                    *id,
                    arguments
                        .iter()
                        .map(|argument| self.at_depth(argument, depth + 1))
                        .collect::<Result<_, _>>()?,
                )
            }
            D::ExternalNominal {
                declaration,
                arguments,
            } => {
                // This is intentionally a current-TCX projection. Neither a
                // diagnostic-item spelling nor the owned observation map can
                // turn an arbitrary external struct into int or nat.
                let scalar = self
                    .meanings
                    .get(self.tcx, declaration.key)
                    .ok_or("an external signature type has no matched native meaning")?;
                if declaration.type_parameters != 0
                    || !arguments.is_empty()
                    || declaration.artifact_sha256 != scalar.artifact()
                {
                    return Err(
                        "a scalar signature type has different binders or selected bytes".into(),
                    );
                }
                Ty::Int(match scalar.kind() {
                    meaning::ScalarKind::Integer => IntRange::Int,
                    meaning::ScalarKind::Natural => IntRange::Nat,
                })
            }
        })
    }
}
