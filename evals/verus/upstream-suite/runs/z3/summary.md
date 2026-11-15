# Verus test suite, solver label `z3`

- Solver (VERUS_Z3_PATH): `~/verus/source/target-verus/debug/z3`
- Invocation 1: started 2026-09-23T18:03:24, 128 binaries, wall 215.2 s, 3 binaries x 3 test threads at once
- Sum of per-binary wall times: 594.3 s
- Binaries run: 128 of 129 test binaries (excluded: cargo)

## Totals

| tests | ok | FAILED | ignored | timeout | crashed | not-run |
|---|---|---|---|---|---|---|
| 4213 | 4114 | 0 | 80 | 0 | 0 | 19 |

Pass rate over tests that ran (excludes ignored and not-run): 4114/4114 = 100.00%

- Verus checkout write check after invocation 1: ~/verus/.git directory mtime only (18:05 manual `git status` in ~/verus for ENV.md, and the runner's own `git status` at 18:07:01, each creating and removing .git/index.lock; .git/index itself unchanged since 2026-09-20); no other path under ~/verus newer than the run start; git status empty

## Per file

| file | tests | ok | FAILED | ignored | timeout | crashed | not-run | wall s | attempts |
|---|---|---|---|---|---|---|---|---|---|
| adts.rs | 111 | 107 | 0 | 4 | 0 | 0 | 0 | 5.27 | 1 |
| adts_generics.rs | 13 | 13 | 0 | 0 | 0 | 0 | 0 | 0.62 | 1 |
| adts_opaque.rs | 10 | 10 | 0 | 0 | 0 | 0 | 0 | 0.99 | 1 |
| arrays.rs | 21 | 21 | 0 | 0 | 0 | 0 | 0 | 6.45 | 1 |
| assert_bitvector_by.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0.34 | 1 |
| assert_by_compute.rs | 38 | 38 | 0 | 0 | 0 | 0 | 0 | 5.03 | 1 |
| assert_forall_by.rs | 17 | 17 | 0 | 0 | 0 | 0 | 0 | 0.68 | 1 |
| assoc_type_impls.rs | 45 | 45 | 0 | 0 | 0 | 0 | 0 | 3.19 | 1 |
| async_functions.rs | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 2.65 | 1 |
| atomic_lib.rs | 32 | 32 | 0 | 0 | 0 | 0 | 0 | 10.47 | 1 |
| atomics.rs | 25 | 25 | 0 | 0 | 0 | 0 | 0 | 7.1 | 1 |
| basic.rs | 60 | 59 | 0 | 1 | 0 | 0 | 0 | 1.65 | 1 |
| bitvector.rs | 83 | 83 | 0 | 0 | 0 | 0 | 0 | 39.74 | 1 |
| boundary_suggestions.rs | 21 | 21 | 0 | 0 | 0 | 0 | 0 | 5.68 | 1 |
| broadcast_forall.rs | 24 | 23 | 0 | 1 | 0 | 0 | 0 | 2.73 | 1 |
| btree.rs | 12 | 12 | 0 | 0 | 0 | 0 | 0 | 4.21 | 1 |
| calc.rs | 5 | 5 | 0 | 0 | 0 | 0 | 0 | 1.73 | 1 |
| cargo.rs | 19 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | 0 |
| cell_lib.rs | 25 | 25 | 0 | 0 | 0 | 0 | 0 | 8.59 | 1 |
| choose.rs | 17 | 17 | 0 | 0 | 0 | 0 | 0 | 0.7 | 1 |
| closures.rs | 8 | 8 | 0 | 0 | 0 | 0 | 0 | 0.38 | 1 |
| consts.rs | 43 | 41 | 0 | 2 | 0 | 0 | 0 | 2.86 | 1 |
| contrib.rs | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0.83 | 1 |
| control_flow.rs | 35 | 35 | 0 | 0 | 0 | 0 | 0 | 2.25 | 1 |
| core_special_setup.rs | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 26.66 | 1 |
| cow.rs | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0.96 | 1 |
| dafny_axioms.rs | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0.85 | 1 |
| default_trait.rs | 24 | 24 | 0 | 0 | 0 | 0 | 0 | 8.67 | 1 |
| eq_cmp.rs | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0.86 | 1 |
| erase.rs | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0.78 | 1 |
| examples.rs | 140 | 140 | 0 | 0 | 0 | 0 | 0 | 47.54 | 1 |
| exec_closures.rs | 88 | 87 | 0 | 1 | 0 | 0 | 0 | 20.38 | 1 |
| exec_spec_unverified.rs | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 1.63 | 1 |
| exec_spec_verified.rs | 32 | 31 | 0 | 1 | 0 | 0 | 0 | 12.07 | 1 |
| exec_termination.rs | 24 | 24 | 0 | 0 | 0 | 0 | 0 | 2.65 | 1 |
| expand_errors.rs | 17 | 15 | 0 | 2 | 0 | 0 | 0 | 1.15 | 1 |
| expr_stmts.rs | 4 | 2 | 0 | 2 | 0 | 0 | 0 | 0.15 | 1 |
| ext_equal.rs | 29 | 29 | 0 | 0 | 0 | 0 | 0 | 8.29 | 1 |
| external_fn_specification.rs | 80 | 77 | 0 | 3 | 0 | 0 | 0 | 2.04 | 1 |
| external_traits.rs | 31 | 31 | 0 | 0 | 0 | 0 | 0 | 2.15 | 1 |
| external_type_specification.rs | 33 | 33 | 0 | 0 | 0 | 0 | 0 | 1.94 | 1 |
| float.rs | 14 | 14 | 0 | 0 | 0 | 0 | 0 | 3.09 | 1 |
| fndef_types.rs | 62 | 61 | 0 | 1 | 0 | 0 | 0 | 5.67 | 1 |
| functions.rs | 10 | 10 | 0 | 0 | 0 | 0 | 0 | 0.38 | 1 |
| generics.rs | 7 | 7 | 0 | 0 | 0 | 0 | 0 | 1.11 | 1 |
| harness.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0.25 | 1 |
| hash.rs | 21 | 21 | 0 | 0 | 0 | 0 | 0 | 8.86 | 1 |
| impl.rs | 16 | 15 | 0 | 1 | 0 | 0 | 0 | 0.53 | 1 |
| inline.rs | 11 | 11 | 0 | 0 | 0 | 0 | 0 | 0.93 | 1 |
| integer_ring.rs | 18 | 0 | 0 | 18 | 0 | 0 | 0 | 0.0 | 0 |
| integers.rs | 37 | 37 | 0 | 0 | 0 | 0 | 0 | 3.54 | 1 |
| layout.rs | 26 | 26 | 0 | 0 | 0 | 0 | 0 | 7.49 | 1 |
| let_else.rs | 7 | 7 | 0 | 0 | 0 | 0 | 0 | 0.3 | 1 |
| lifetime.rs | 103 | 100 | 0 | 3 | 0 | 0 | 0 | 8.09 | 1 |
| literals.rs | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 1.57 | 1 |
| loops.rs | 64 | 62 | 0 | 2 | 0 | 0 | 0 | 4.15 | 1 |
| loops_no_spinoff.rs | 60 | 60 | 0 | 0 | 0 | 0 | 0 | 4.04 | 1 |
| maps.rs | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 2.58 | 1 |
| marker_traits.rs | 59 | 59 | 0 | 0 | 0 | 0 | 0 | 13.81 | 1 |
| match.rs | 50 | 50 | 0 | 0 | 0 | 0 | 0 | 3.18 | 1 |
| modes.rs | 118 | 116 | 0 | 2 | 0 | 0 | 0 | 6.5 | 1 |
| modules.rs | 27 | 25 | 0 | 2 | 0 | 0 | 0 | 0.66 | 1 |
| multiset.rs | 5 | 5 | 0 | 0 | 0 | 0 | 0 | 1.56 | 1 |
| mut_refs.rs | 112 | 112 | 0 | 0 | 0 | 0 | 0 | 11.25 | 1 |
| mut_refs_closures.rs | 14 | 14 | 0 | 0 | 0 | 0 | 0 | 2.95 | 1 |
| mut_refs_libs.rs | 7 | 7 | 0 | 0 | 0 | 0 | 0 | 2.71 | 1 |
| mut_refs_loops.rs | 29 | 29 | 0 | 0 | 0 | 0 | 0 | 2.39 | 1 |
| mut_refs_modes.rs | 121 | 120 | 0 | 1 | 0 | 0 | 0 | 7.96 | 1 |
| mut_refs_old.rs | 27 | 27 | 0 | 0 | 0 | 0 | 0 | 2.19 | 1 |
| mut_refs_patterns.rs | 72 | 72 | 0 | 0 | 0 | 0 | 0 | 4.35 | 1 |
| mut_refs_slices_arrays.rs | 30 | 30 | 0 | 0 | 0 | 0 | 0 | 10.18 | 1 |
| mut_refs_temporaries.rs | 19 | 19 | 0 | 0 | 0 | 0 | 0 | 2.25 | 1 |
| mut_refs_time_travel.rs | 92 | 76 | 0 | 16 | 0 | 0 | 0 | 5.32 | 1 |
| mut_refs_unions.rs | 30 | 28 | 0 | 2 | 0 | 0 | 0 | 6.23 | 1 |
| mutable_params.rs | 11 | 11 | 0 | 0 | 0 | 0 | 0 | 1.17 | 1 |
| nested_items.rs | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0.14 | 1 |
| never_type.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0.72 | 1 |
| no_cheating.rs | 10 | 10 | 0 | 0 | 0 | 0 | 0 | 0.82 | 1 |
| nonlinear.rs | 19 | 18 | 0 | 1 | 0 | 0 | 0 | 0.98 | 1 |
| opaque_reveal.rs | 28 | 24 | 0 | 4 | 0 | 0 | 0 | 1.31 | 1 |
| opaque_types.rs | 21 | 21 | 0 | 0 | 0 | 0 | 0 | 6.2 | 1 |
| open_invariant.rs | 67 | 67 | 0 | 0 | 0 | 0 | 0 | 15.07 | 1 |
| operators.rs | 12 | 12 | 0 | 0 | 0 | 0 | 0 | 2.88 | 1 |
| option.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 1.77 | 1 |
| output_json.rs | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 0.35 | 1 |
| overflow.rs | 24 | 24 | 0 | 0 | 0 | 0 | 0 | 2.39 | 1 |
| partial_eq.rs | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0.0 | 0 |
| proof_closures.rs | 105 | 105 | 0 | 0 | 0 | 0 | 0 | 27.86 | 1 |
| proof_in_spec.rs | 30 | 30 | 0 | 0 | 0 | 0 | 0 | 0.98 | 1 |
| proph.rs | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 1.41 | 1 |
| prophecy.rs | 51 | 51 | 0 | 0 | 0 | 0 | 0 | 1.62 | 1 |
| quantifiers.rs | 18 | 18 | 0 | 0 | 0 | 0 | 0 | 1.69 | 1 |
| raw_ptrs.rs | 10 | 10 | 0 | 0 | 0 | 0 | 0 | 2.72 | 1 |
| real.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0.26 | 1 |
| recommends.rs | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0.76 | 1 |
| recursion.rs | 109 | 109 | 0 | 0 | 0 | 0 | 0 | 8.4 | 1 |
| recursive_types.rs | 23 | 23 | 0 | 0 | 0 | 0 | 0 | 5.1 | 1 |
| refs.rs | 38 | 36 | 0 | 2 | 0 | 0 | 0 | 2.83 | 1 |
| regression.rs | 87 | 86 | 0 | 1 | 0 | 0 | 0 | 12.45 | 1 |
| results.rs | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0.85 | 1 |
| return.rs | 13 | 13 | 0 | 0 | 0 | 0 | 0 | 1.19 | 1 |
| returns_postcondition.rs | 14 | 14 | 0 | 0 | 0 | 0 | 0 | 0.5 | 1 |
| safe_api.rs | 34 | 34 | 0 | 0 | 0 | 0 | 0 | 1.08 | 1 |
| scope.rs | 10 | 10 | 0 | 0 | 0 | 0 | 0 | 0.44 | 1 |
| seqs.rs | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 1.91 | 1 |
| sets.rs | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 2.47 | 1 |
| size_of.rs | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0.99 | 1 |
| slices.rs | 8 | 8 | 0 | 0 | 0 | 0 | 0 | 2.84 | 1 |
| spec_derive.rs | 19 | 19 | 0 | 0 | 0 | 0 | 0 | 3.23 | 1 |
| state_machines.rs | 226 | 225 | 0 | 1 | 0 | 0 | 0 | 19.77 | 1 |
| std.rs | 30 | 30 | 0 | 0 | 0 | 0 | 0 | 8.42 | 1 |
| strings.rs | 42 | 42 | 0 | 0 | 0 | 0 | 0 | 11.62 | 1 |
| structural.rs | 5 | 5 | 0 | 0 | 0 | 0 | 0 | 0.91 | 1 |
| summer_school.rs | 32 | 30 | 0 | 2 | 0 | 0 | 0 | 6.0 | 1 |
| syntax_attr.rs | 65 | 65 | 0 | 0 | 0 | 0 | 0 | 8.25 | 1 |
| traits.rs | 212 | 210 | 0 | 2 | 0 | 0 | 0 | 12.59 | 1 |
| traits_dyn.rs | 22 | 22 | 0 | 0 | 0 | 0 | 0 | 4.62 | 1 |
| traits_extend_ensures.rs | 25 | 25 | 0 | 0 | 0 | 0 | 0 | 1.24 | 1 |
| traits_modules.rs | 37 | 37 | 0 | 0 | 0 | 0 | 0 | 2.13 | 1 |
| traits_modules_pub_crate.rs | 37 | 37 | 0 | 0 | 0 | 0 | 0 | 1.85 | 1 |
| triggers.rs | 33 | 33 | 0 | 0 | 0 | 0 | 0 | 2.74 | 1 |
| ui.rs | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0.13 | 1 |
| unions.rs | 28 | 27 | 0 | 1 | 0 | 0 | 0 | 1.85 | 1 |
| unsafe.rs | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0.13 | 1 |
| unwind.rs | 12 | 12 | 0 | 0 | 0 | 0 | 0 | 1.83 | 1 |
| user_defined_type_invariants.rs | 78 | 78 | 0 | 0 | 0 | 0 | 0 | 2.86 | 1 |
| vec.rs | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 1.02 | 1 |
| when_used_as_spec.rs | 16 | 16 | 0 | 0 | 0 | 0 | 0 | 1.23 | 1 |
| z3_restart.rs | 7 | 7 | 0 | 0 | 0 | 0 | 0 | 0.79 | 1 |

## Not run

- `cargo` (cargo.rs): invokes `cargo`/`cargo verus` builds (PATH cargo is a reroute here); not run
- `cargo_verus` (deps binary with no tests/cargo_verus.rs): identical to target-verus/debug/cargo-verus; a tool binary, not a libtest harness
- `rust_verify` (deps binary with no tests/rust_verify.rs): identical to target-verus/debug/rust_verify; a tool binary, not a libtest harness
- `verus` (deps binary with no tests/verus.rs): identical to target-verus/debug/verus; a tool binary, not a libtest harness
- `vstd_build` (deps binary with no tests/vstd_build.rs): no tests/<name>.rs source; not a libtest harness (not run)

## Tests not ok and not ignored (0)

None.
