# basic_big_and_syntax_vs_forall — rust-error cargo fixture (upstream basic.rs `test_big_and_syntax_vs_forall`)

Standalone cargo fixture reproducing the upstream Rust-channel error case
`test_big_and_syntax_vs_forall` (`assert_rust_error_msg(e, "cannot find value
\`i\`")`, rustc E0425). Upstream:

```verus
spec fn test() -> bool {
    &&& forall|i: int| true
    &&& i == 0
}
```

The pinned behavior is a BINDER-SCOPING fact: the `forall` binder `i` scopes
only over its own `&&&` bullet, so the `i` in the second bullet is unresolved
— a Rust name-resolution error, not a verifier diagnostic. The trust-vc
compiled-surface mirror keeps exactly that structure (`trust_vc::forall!`
closure binder + plain conjunction — `&&&` bullets are macro-token-only
surface, not compilable Rust):

```rust
#[trust_vc::spec]
pub fn test() -> bool {
    trust_vc::forall!(|i: int| true) && i == 0
}
```

Verified with a real `cargo check --message-format=json`: exit code 101,
exactly ONE error-level diagnostic with a primary span in `src/lib.rs`:

    E0425: error[E0425]: cannot find value `i` in this scope

matched by substring against the harvested upstream pattern
"cannot find value `i`".

## Status: NOT yet wired into the manifest

Same situation as `../basic_fail_assign_non_mut` (see its README for the full
rationale): basic.rs is `unsupported-gap` and its scout expected_cases are
pinned by the scout-const inventory, the regression-test metadata pins, and
the all-cases-must-bind-paths rule — so this fixture is parked unreferenced
(inert to the gate) until the promotion commit.

## Promotion-time wiring

```json
{
  "case_id": "test_big_and_syntax_vs_forall",
  "upstream_case_id": "test_big_and_syntax_vs_forall",
  "trust_vc_path": "evals/verus/ported/basic_big_and_syntax_vs_forall",
  "expected_verdict": "error",
  "min_obligations": 0,
  "expected_error_patterns": ["cannot find value `i`"]
}
```

plus the entry-level `trust_vc_paths` addition and the case-level path
bindings on the sibling cases (documented in
`../basic_fail_assign_non_mut/README.md`).
