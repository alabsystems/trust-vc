// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Only the normal call successor can recover matched captured ownership.
use super::*;

#[derive(Default)]
pub(super) struct CallOutput {
    pub(super) loans: Vec<(Place, Vec<Place>)>,
    pub(super) aliases: Vec<(Place, Vec<Place>)>,
}

impl Builder<'_, '_> {
    pub(super) fn finish_call(
        &self,
        state: &mut OwnershipState,
        call: usize,
        dest: Option<&Place>,
    ) -> R<CallOutput> {
        let Some(pending) = state.pending_call.take() else {
            return Ok(CallOutput::default());
        };
        if pending.call != call {
            return Ok(CallOutput::default());
        }
        if let Some(dest) = dest {
            if !self.kept_place(dest)? {
                // A ghost snapshot is not an owned result destination.
                return Ok(CallOutput::default());
            }
        }
        pending.price(&self.work, self.decl.span)?;
        // This restoration happens BEFORE the normal destination overwrite;
        // any old destination's surviving pointees can add further escapes.
        state.escaped = pending.escaped_before;
        let mut output = CallOutput::default();
        for argument in pending.arguments {
            for origin in argument.extras {
                self.union(&mut state.escaped, &origin.loans)?;
            }
            for row in argument.rows {
                let mut selected = None;
                let mut ambiguous = false;
                for binding in &pending.bindings {
                    self.charge(1 + row.path.len() + binding.argument.len())?;
                    if binding.parameter == argument.parameter
                        && row.path.starts_with(&binding.argument)
                    {
                        if selected.is_some() {
                            ambiguous = true;
                        }
                        selected = Some(binding);
                    }
                }
                let Some(binding) = selected.filter(|_| !ambiguous) else {
                    self.union(&mut state.escaped, &row.loans)?;
                    continue;
                };
                if let Some(dest) = dest {
                    self.charge(
                        1 + dest.projections.len() + binding.result.len() + row.path.len(),
                    )?;
                    let mut owner = dest.clone();
                    owner.projections.extend_from_slice(&binding.result);
                    owner
                        .projections
                        .extend_from_slice(&row.path[binding.argument.len()..]);
                    if let Some(aliases) = row.aliases {
                        self.work
                            .places(std::slice::from_ref(&owner), self.decl.span)?;
                        output.aliases.push((owner.clone(), aliases));
                    }
                    output.loans.push((owner, row.loans));
                } else if row.path.len() != binding.argument.len() {
                    // Dropping the returned outer carrier never resolves its
                    // dereferenced contents. Those values survive elsewhere.
                    self.preserve_discarded_contents(state, row)?;
                }
            }
        }
        Ok(output)
    }

    fn preserve_discarded_contents(&self, state: &mut OwnershipState, row: CapturedRow) -> R<()> {
        let Some(survivors) = row.survivors else {
            return self.union(&mut state.escaped, &row.loans);
        };
        let exact = survivors.len() == 1;
        for owner in survivors {
            self.charge((1 + owner.projections.len()).saturating_mul(
                1 + state.declared.len() + state.initialized.len() + state.moved.len(),
            ))?;
            let available = state.declared.contains(&owner.local)
                && state.is_initialized(&owner)
                && !state.moved.iter().any(|moved| overlaps(moved, &owner));
            if !available {
                self.union(&mut state.escaped, &row.loans)?;
                continue;
            }
            self.work
                .places(std::slice::from_ref(&owner), self.decl.span)?;
            self.union(state.loans.entry(owner.clone()).or_default(), &row.loans)?;
            match &row.aliases {
                Some(aliases) if exact => {
                    self.union(state.aliases.entry(owner).or_default(), aliases)?
                }
                Some(aliases) => {
                    if let Some(old) = state.aliases.get_mut(&owner) {
                        self.union(old, aliases)?;
                    }
                }
                None => {
                    state.aliases.remove(&owner);
                }
            }
        }
        Ok(())
    }

    pub(super) fn stable_result_aliases(
        &self,
        state: &OwnershipState,
        rows: &mut Vec<(Place, Vec<Place>)>,
        dest: &Place,
        writes: &[Place],
    ) -> R<()> {
        let mut stable = Vec::new();
        for (index, (_, targets)) in rows.iter().enumerate() {
            let mut valid = !targets.is_empty();
            for target in targets {
                self.charge(
                    (1 + target.projections.len())
                        .saturating_mul(1 + state.declared.len() + state.moved.len() + writes.len())
                        .saturating_add(dest.projections.len()),
                )?;
                valid &= !target.has_deref()
                    && state.declared.contains(&target.local)
                    && !state.moved.iter().any(|moved| overlaps(moved, target))
                    && !overlaps(dest, target)
                    && !writes.iter().any(|written| overlaps(written, target));
            }
            if valid {
                self.charge(1)?;
                stable.push(index);
            }
        }
        self.charge(rows.len().saturating_mul(1 + stable.len()))?;
        let mut index = 0;
        rows.retain(|_| {
            let keep = stable.contains(&index);
            index += 1;
            keep
        });
        Ok(())
    }
}
