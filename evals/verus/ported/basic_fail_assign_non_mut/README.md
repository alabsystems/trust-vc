# basic_fail_assign_non_mut — rust-error cargo fixture (upstream basic.rs `test_fail_assign_non_mut`)

Standalone cargo fixture reproducing the upstream Rust-channel error case
`test_fail_assign_non_mut` (`assert_rust_error_msg(err, "cannot assign twice
to immutable variable")`, rustc E0384). Verified with a real `cargo check
--message-format=json`: exit code 101, exactly ONE error-level diagnostic with
a primary span in `src/lib.rs`:

    E0384: error[E0384]: cannot assign twice to immutable variable `x`

which the evidence gate's cargo-fixture rust-error channel
(`run_trust_vc_corpus_cargo_fixture_source_errors`,
`rust_source_error_diagnostics_from_cargo_json` in
`crates/cargo-trust-vc/src/evidence.rs`) matches by substring against
`expected_error_patterns`.

## Status: NOT yet wired into the manifest

`source/rust_verify_test/tests/basic.rs` is classified `unsupported-gap`; its
scout expected_cases are pinned three ways the gate validates for gap entries
(the `BASIC_RS_EXPECTED_CASES` const inventory in `evals/verus/ported/basic.rs`
via `append_unsupported_scout_inventory_failures`, the exact-metadata pins in
`crates/trust-vc/tests/basic_rs_trust_vc_regressions.rs`, and the
one-case-declares-a-path ⇒ all-cases-must-declare-paths rule at
`evidence.rs::run_candidates_for_manifest_entry`/manifest validation), so
referencing this fixture from the gap entry today would require touching all
three surfaces for zero gate progress. Per the slice mandate the fixture is
therefore parked here unreferenced (manifest-referenced paths only are read by
the gate — unreferenced directories are inert).

## Promotion-time wiring (the erase.rs / maps.rs / functions.rs pattern)

When basic.rs flips to `ported`, the entry gains:

```json
"trust_vc_paths": [
  "evals/verus/ported/basic.rs",
  "evals/verus/ported/basic_fail_assign_non_mut",
  "evals/verus/ported/basic_big_and_syntax_vs_forall"
],
```

and an expected case (case-level `trust_vc_path` binding is REQUIRED once the
accepted entry has more than one path):

```json
{
  "case_id": "test_fail_assign_non_mut",
  "upstream_case_id": "test_fail_assign_non_mut",
  "trust_vc_path": "evals/verus/ported/basic_fail_assign_non_mut",
  "expected_verdict": "error",
  "min_obligations": 0,
  "expected_error_patterns": ["cannot assign twice to immutable variable"]
}
```

The pattern string is exactly the literal the upstream harness extractor
harvests from `assert_rust_error_msg`, so the accepted-entry upstream
cross-check (`evidence.rs` ~4419: rust_error cases must map to a cargo-fixture
trust_vc_path and declare the harvested pattern verbatim) passes. Every other
basic.rs expected case must then also declare
`"trust_vc_path": "evals/verus/ported/basic.rs"`, and the
`basic_rs_trust_vc_regressions` metadata pins updated in the same commit.
