// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection ground-term seeding for quantified array properties.

use ay_dpll::api::Sort;

use crate::encoder::types::sort_for_type;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

use super::encoding_error;

impl AYEncoder {
    /// Seeds ground `select(array, 0)` terms for collection variables in scope.
    ///
    /// When arrays are purely symbolic (no concrete element accesses at depth 0),
    /// ay-dpll's E-matching has no ground trigger terms to instantiate quantified
    /// array properties from. This method creates a ground select at index 0 for
    /// each collection variable, giving E-matching a starting point.
    ///
    /// ay's multi-round E-matching chains from the seed:
    /// given `select(a, 0)`, a sortedness axiom `forall j: a[j] <= a[j+1]` fires
    /// with `j=0`, producing `select(a, 1)`, which triggers `j=1`, etc.
    ///
    /// Call once after all broadcasts are asserted to avoid duplicate seeding.
    /// Part of #2390.
    pub(in crate::encoder) fn seed_collection_ground_selects(&mut self) -> TrustVcResult<()> {
        let collection_vars: Vec<(String, TrustVcType, ay_dpll::api::Term)> = self
            .var_types
            .iter()
            .filter(|(_, ty)| ty.is_collection())
            .filter_map(|(name, ty)| {
                self.variables
                    .get(name)
                    .map(|&term| (name.clone(), ty.clone(), term))
            })
            .collect();

        if collection_vars.is_empty() {
            return Ok(());
        }

        for (name, ty, var_term) in collection_vars {
            #[cfg(feature = "native-seq")]
            if let TrustVcType::Seq(ref elem) | TrustVcType::Array(ref elem, _) = ty {
                let elem_sort = sort_for_type(elem);
                let idx_zero = self.solver.int_const(0);
                let elem_term = self.solver.try_seq_nth(var_term, idx_zero).map_err(|e| {
                    encoding_error(
                        "seed ground seq.nth",
                        format!("Failed to create seq.nth({}, 0): {}", name, e),
                    )
                })?;
                let seed_name = format!("__ground_seed_{}", name);
                let seed_const = self.solver.declare_const(&seed_name, elem_sort);
                let eq = self.solver.try_eq(seed_const, elem_term).map_err(|e| {
                    encoding_error(
                        "seed ground seq.nth",
                        format!("Failed to bind ground seed for '{}': {}", name, e),
                    )
                })?;
                self.solver.try_assert_term(eq).map_err(|e| {
                    encoding_error(
                        "seed ground seq.nth",
                        format!("Failed to assert ground seed for '{}': {}", name, e),
                    )
                })?;
                continue;
            }

            let (index_sort, elem_sort) = match &ty {
                TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => (
                    Sort::bitvec(crate::ir::pointer_width()),
                    sort_for_type(elem),
                ),
                TrustVcType::Map(key, val) => (sort_for_type(key), sort_for_type(val)),
                TrustVcType::Set(elem) => (sort_for_type(elem), Sort::Bool),
                _ => continue,
            };

            // A DATATYPE-VALUED MAP gets no seed. The seed only names
            // `select(data, 0)` for an E-matching start, and index 0 is not a
            // distinguished key of a map (a Seq keeps its seed: there it is the
            // first element). For a `Map<_, <datatype>>` that named read is the
            // one thing that drags the datatype-valued array into the model:
            // measured 2026-09-13 at ay 0.26.0 on the `Map<u32, (u32, u32)>` liar
            // `m.get(1).1 == 999` — the goal folds to `(not (= (T_1 (T 7 8))
            // 999))`, which ay decides `sat` in 1 ms with the seed removed and
            // answers `Unknown (incomplete)` with it
            // (`collection_tuple_element_capability::map_tuple_false_counterexamples`,
            // red since a15b6207). The seed is a fresh constant bound by one
            // equality, so omitting it drops a conservative definition: it can
            // lose an E-matching instance, never make a false claim `Verified`.
            if let TrustVcType::Map(_, value_ty) = &ty {
                if matches!(
                    value_ty.as_ref(),
                    TrustVcType::Datatype { .. } | TrustVcType::RecursiveRef(_)
                ) {
                    continue;
                }
            }

            let idx_zero = match &index_sort {
                Sort::BitVec(bvs) => self.solver.try_bv_const(0, bvs.width).map_err(|e| {
                    encoding_error(
                        "seed ground select",
                        format!("Failed to create BV(0) for '{}': {}", name, e),
                    )
                })?,
                Sort::Int => self.solver.int_const(0),
                Sort::Bool => self.solver.bool_const(false),
                _ => continue,
            };

            let elem_term = self.solver.try_select(var_term, idx_zero).map_err(|e| {
                encoding_error(
                    "seed ground select",
                    format!("Failed to create select({}, 0): {}", name, e),
                )
            })?;

            // Bind to a fresh constant so ay internalizes the select term
            // in the E-matching congruence closure. The fresh constant is
            // unconstrained except for this equality, so the assertion is
            // always satisfiable - it just names the element at index 0.
            let seed_name = format!("__ground_seed_{}", name);
            let seed_const = self.solver.declare_const(&seed_name, elem_sort);
            let eq = self.solver.try_eq(seed_const, elem_term).map_err(|e| {
                encoding_error(
                    "seed ground select",
                    format!("Failed to bind ground seed for '{}': {}", name, e),
                )
            })?;
            self.solver.try_assert_term(eq).map_err(|e| {
                encoding_error(
                    "seed ground select",
                    format!("Failed to assert ground seed for '{}': {}", name, e),
                )
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::VariableDecl;
    use ay_dpll::api::TermKind;

    #[cfg(not(feature = "native-seq"))]
    #[test]
    fn test_seed_collection_ground_selects_asserts_seq_seed_equality() {
        let mut encoder = AYEncoder::new();
        encoder
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name: "s".to_string(),
                ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 64 })),
            })
            .expect("Seq variable declaration should succeed");
        let baseline_assertions = encoder.solver.assertions().len();

        encoder
            .seed_collection_ground_selects()
            .expect("seed_collection_ground_selects should succeed");

        let assertions = encoder.solver.assertions();
        assert!(
            assertions.len() > baseline_assertions,
            "seeding should add at least one solver assertion"
        );

        let seed_assertion = assertions
            .into_iter()
            .find(|&term| {
                let children = encoder.solver.term_children(term);
                let has_seed_var = children.iter().any(|&child| {
                    matches!(
                        encoder.solver.term_kind(child),
                        TermKind::Var { ref name } if name == "__ground_seed_s"
                    )
                });
                let has_select = children.iter().any(|&child| {
                    matches!(
                        encoder.solver.term_kind(child),
                        TermKind::App { ref name, num_args: 2 } if name == "select"
                    )
                });
                children.len() == 2 && has_seed_var && has_select
            })
            .expect("seeding should assert __ground_seed_s == select(s, 0)");

        let negated = encoder
            .solver
            .try_not(seed_assertion)
            .expect("seed assertion should be Boolean");
        encoder
            .solver
            .try_assert_term(negated)
            .expect("negated seed assertion should assert cleanly");

        let sat = encoder
            .solver
            .try_check_sat()
            .expect("seed contradiction should solve");
        assert!(
            sat.is_unsat(),
            "negating the asserted ground seed equality should be unsat, got: {sat:?}"
        );
    }

    #[cfg(feature = "native-seq")]
    #[test]
    fn test_seed_collection_ground_selects_uses_seq_nth_for_native_seq() {
        let mut encoder = AYEncoder::new();
        encoder
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name: "s".to_string(),
                ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 64 })),
            })
            .expect("Seq variable declaration should succeed");

        encoder
            .seed_collection_ground_selects()
            .expect("native-seq seeding should succeed");

        let seed_assertion = encoder
            .solver
            .assertions()
            .into_iter()
            .find(|&term| {
                let children = encoder.solver.term_children(term);
                let has_seed_var = children.iter().any(|&child| {
                    matches!(
                        encoder.solver.term_kind(child),
                        TermKind::Var { ref name } if name == "__ground_seed_s"
                    )
                });
                let has_seq_nth = children.iter().any(|&child| {
                    matches!(
                        encoder.solver.term_kind(child),
                        TermKind::App { ref name, num_args: 2 } if name == "seq.nth"
                    )
                });
                children.len() == 2 && has_seed_var && has_seq_nth
            })
            .expect("native-seq seeding should assert __ground_seed_s == seq.nth(s, 0)");

        let negated = encoder
            .solver
            .try_not(seed_assertion)
            .expect("seed assertion should be Boolean");
        encoder
            .solver
            .try_assert_term(negated)
            .expect("negated seed assertion should assert cleanly");

        let solve = encoder
            .solver
            .try_check_sat()
            .expect("seed contradiction should solve");
        let sat = solve.result();
        assert!(
            sat.is_unsat(),
            "negating the asserted native-seq seed equality should be unsat, got: {sat:?}"
        );
    }

    #[test]
    fn test_seed_collection_ground_selects_ignores_scalar_variables() {
        let mut encoder = AYEncoder::new();
        encoder
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 64 },
            })
            .expect("scalar variable declaration should succeed");
        let baseline_assertions = encoder.solver.assertions().len();

        encoder
            .seed_collection_ground_selects()
            .expect("scalar-only seeding should succeed");

        assert_eq!(
            encoder.solver.assertions().len(),
            baseline_assertions,
            "scalar variables should not produce ground seed assertions"
        );
    }
}
