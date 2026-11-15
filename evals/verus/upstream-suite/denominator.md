# Denominator: static cases vs. tests in the prebuilt binaries

Static source: `<verus>/source/rust_verify_test/tests` at Verus a40d57c7. Runtime: `--list` of the prebuilt binaries in `<verus>/source/target.noindex/debug/deps`.

## Summary

- The binaries contain **4213** #[test] functions, and 80 of them are `#[ignore]`.
- The static figure of 3,849 is 3774 non-ignored named `test_verify_one_file` cases plus 75 `test_verify_one_bv_file` cases.
- 3 of those 3774 cases are `#[cfg(target_pointer_width = "32")]` in layout.rs and are not compiled on this 64-bit host. The binaries therefore hold 3771 + 75 = 3846 of them.
- Each bv test verifies its case twice: once with bit-vector simplification and once with `no-bv-simplify`.
- The static count leaves out these runtime tests:
  - 80 ignored named cases;
  - 122 tests that local `macro_rules!` generate from the 20 unnamed templates;
  - 140 `examples_in_dir!` tests, one per example file;
  - 19 `cargo.rs` tests;
  - 6 plain `#[test] fn`s in harness.rs and summer_school.rs.
- Check: 3771 + 75 + 80 + 122 + 140 + 19 + 6 = 4213.

## Static count

| item | count |
|---|---|
| `test_verify_one_file[_with_options]!` invocations (all) | 3874 |
| of those: named `#[test]`, not ignored | 3774 |
| of those: named `#[test]`, `#[ignore]` (incl. cfg_attr ignore) | 80 |
| of those: no `#[test] name` in the block (templates inside `macro_rules!`, name is `$name`) | 20 |
| of those: inside a `macro_rules!` body | 20 |
| of those: commented out | 0 |
| `test_verify_one_bv_file[_with_options]!` invocations | 75 (named, not ignored: 75; ignored: 0) |

## Runtime count (libtest `--list`, 129 test binaries incl. cargo)

| item | count |
|---|---|
| #[test] functions | 4213 |
| of which `#[ignore]` | 80 |
| matched to a named `test_verify_one_file` case | 3851 |
| matched to a named `test_verify_one_bv_file` case (one test runs the case twice: bv simplify on, then off) | 75 |
| not from a named static case (see below) | 287 |
| named static cases with no runtime test | 3 |

## Runtime tests that are not a named static case, by file

| file | tests | ignored | how they are generated | examples |
|---|---|---|---|---|
| examples.rs | 140 | 0 | `examples_in_dir!`: one test per .rs file under <verus>/examples (8 dirs) | examples_adts, examples_adts_eq, examples_assert_by_compute ... |
| marker_traits.rs | 59 | 0 | a local `macro_rules!` that expands to `test_verify_one_file!` (one of the 20 unnamed templates) | atomic_invariant, atomic_invariant2, atomic_none ... |
| open_invariant.rs | 46 | 0 | a local `macro_rules!` that expands to `test_verify_one_file!` (one of the 20 unnamed templates) | basic_usage, basic_usage2, basic_usage2_local ... |
| cargo.rs | 19 | 0 | `cargo_examples!` (17 dirs under tests/cargo-tests) + 2 plain #[test] fns; they run `cargo` | cargo_new_builds, cargo_new_verifies, unverified_consume_basic_verified_lib ... |
| default_trait.rs | 11 | 0 | a local `macro_rules!` that expands to `test_verify_one_file!` (one of the 20 unnamed templates) | test_default_bool_ok, test_default_bool_wrong, test_default_f32_ok ... |
| adts.rs | 6 | 0 | a local `macro_rules!` that expands to `test_verify_one_file!` (one of the 20 unnamed templates) | matches_syntax_precedence_4a, matches_syntax_precedence_4b, matches_syntax_precedence_5 ... |
| harness.rs | 4 | 0 | plain #[test] fns that call verify_one_file directly | harness_false, harness_invalid_rust, harness_true ... |
| summer_school.rs | 2 | 0 | plain #[test] fns that call verify_files (multi-file) | e10_pass, e13_pass |

## Reconciliation with run `z3`

| static source | outcome | tests |
|---|---|---|
| bv | ok | 75 |
| other | not-run | 19 |
| other | ok | 268 |
| tvof | ignored | 80 |
| tvof | ok | 3771 |

## Named static cases with no runtime test

- layout.rs:230 `test_set_to_64_on_32_bit_compile` (test_verify_one_file_with_options)
- layout.rs:240 `test_set_to_32_on_32_bit_compile` (test_verify_one_file_with_options)
- layout.rs:476 `test_cfg_global_layout_usize_32` (test_verify_one_file_with_options)
