// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Charged provenance lookup and availability of locally owned loan carriers.
use super::*;

impl Gen<'_> {
    pub(super) fn reference_origin(&self, term: &Term) -> R<Term> {
        let mut current = term;
        // Existing aliases point to older terms. Loop cuts bind loan records
        // to fresh carriers instead of installing cross-iteration aliases.
        for _ in 0..=self.reference_aliases.len() + self.reference_aliases.len() + 64 {
            self.resolution.charge(1, self.decl.span)?;
            if let Some(previous) = self.reference_aliases.get(current) {
                current = previous;
                continue;
            }
            if let Term::Call { name, args, .. } = current {
                if name == "mut_ref_update_current" && args.len() == 2 {
                    current = &args[0];
                    continue;
                }
            }
            self.price_ownership_term(current, self.decl.span)?;
            return Ok(current.clone());
        }
        Err(refusal(
            "resolution-origin",
            "cyclic reference provenance",
            self.decl.span,
        ))
    }

    pub(super) fn reference_resolved(&self, path: &Path, reference: &Term) -> R<bool> {
        let origin = self.reference_origin(reference)?;
        for resolved in &path.resolved {
            if self.reference_origin(resolved)? == origin {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn active_borrows(&self, path: &Path) -> R<Vec<Place>> {
        let mut places = Vec::new();
        for loan in &path.loans {
            if !self.reference_resolved(path, &loan.reference)? {
                for place in &loan.places {
                    self.price_ownership_place(place, self.decl.span)?;
                    places.push(place.clone());
                }
            }
        }
        for place in &path.escaped_loans {
            self.price_ownership_place(place, self.decl.span)?;
            places.push(place.clone());
        }
        Ok(places)
    }
}
