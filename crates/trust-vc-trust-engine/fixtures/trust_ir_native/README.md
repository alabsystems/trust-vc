# Native TrustIr Bundle Fixtures

`native_request_trust_bundle.json` is copied from TrustIr's conformance corpus at
rev `ba039cfea77ae44eeaba0dc8e2946c27d5d97ddd`
(`crates/trust-ir-conformance/tests/fixtures/native_request_trust_bundle.json`,
bundle schema 9), the trust-ir rev this workspace pins. Re-copy it, never edit
it, in the same commit as a pin move: its digests are computed upstream.

It pins direct TrustVc consumption of `trust_ir::NativeVerificationBundle` and its
typed `NativeVerificationRequest::TrustVc` variant. The fixture intentionally
does not use adapter-name strings or source-text verifier payloads, and includes
schema-v5 compiler facts, native assertion ids, replay metadata, and typed
native evidence bundles.

## Discharge-lane fixtures

`discharge_scalar_branch.json`, `discharge_scalar_branch_liar.json`,
`discharge_scalar_inc.json` and `discharge_callee_contract_liar.json` exercise
`TrustVcVerificationMode::DischargeProofObligations` — trust-vc proving a
compiler-minted obligation from the trust-ir body, rather than checking a
certificate somebody else produced.

* `discharge_scalar_branch.json` —
  `fn clamp(x: u32) -> u32 { if x > 10 { 10 } else { x } }` with
  `requires x >= 1` and `ensures result >= 1`. A conditional branch, two arms and
  a block-parameter (phi) join, with a postcondition that genuinely needs the
  precondition. DISCHARGES.
* `discharge_scalar_branch_liar.json` — the same module with one character
  changed, `ensures result >= 2`. REFUTED at `x = 1`. This is the
  mutation-sensitive discriminator: if the lane were rubber-stamping, the twin
  would pass too.
* `discharge_scalar_inc.json` — `fn inc(x: u32) -> u32 { x + 1 }` with
  `ensures result == x + 1`. A DECLINE fixture, and the record of a false
  `Discharged` found in adversarial review: a `trust-types.Formula@1` `Add` is
  MATHEMATICAL integer addition, so deciding it at the operand's declared machine
  width proves a different predicate than the clause spells, and the clause is
  false at `x = u32::MAX` where the wrapping reading is true. The tests drive it
  in three directions — the decline itself, the `MachineArithmetic` premise on an
  arithmetic-free clause over the same (machine-arithmetic) body, and the ay
  certification-funnel refusal at 64 bits, now spelled with the `BvAdd` node that
  denotes the fixed-width operation.
* `discharge_callee_contract_liar.json` — ADVERSARIAL REVIEW ROUND 6, BLOCKER 1.
  `fn caller(x: u32) -> u32 { g(x) }` with `fn g(a: u32) -> u32 { a }`. `g` is
  the IDENTITY, so `g(0) == 0`, yet it publishes `ensures result >= 100` at
  `ProofStatus::Discharged` with NO certificate, and `caller` claims the same.
  The module's ONLY validator error is `DischargedWithoutCertificate` — the one
  verdict the input gate deliberately carries past — so the bare label was the
  whole distance between this bundle and a `verdict=Discharged` with a
  kernel-checked certificate for a claim false at `x = 0`. It now DECLINES:
  `Discharged` is a label, not evidence.

**Hand-authored, and honest about it.** No compiler on this machine can dump
these yet (`-Ztrust-dump=native-bundle` needs a seal that embeds trust-vc at this
revision), so the module, obligations and compiler facts are written by hand in
the shape the producer emits: `trust-types.Formula@1` payloads whose leaves carry
the clause parser's `Sort::Int` placeholder, and whose `result` is spelled `_0`
(`trust_types::spec_parse::map_var_name`). **The public `vc:` obligation ids are
PROVISIONAL** until a dumped bundle reproduces them.

Every identity in them is DERIVED, never hand-written: the module digest and
everything that quotes it are recomputed by trust-ir's own
`Module::stable_digest`, and each request's replay context is rebuilt the way
Trust's `trust-ir-bridge` writes it — one `Assertion` atom per requested
obligation, stating its formula and carrying its compiler-fact assertion id,
which is the only thing the export seam publishes an id from. Regenerate after
editing a fixture by hand:

```sh
TRUST_VC_REGENERATE_DISCHARGE_FIXTURES=1 targo --unverified test \
    -p trust-vc-trust-engine --test native_trust_ir_bundle -- regenerate
```

They carry NO TrustVc certificate and NO TrustVc evidence bundle, which is what
a discharge request looks like: both are what the mode PRODUCES. trust-ir's
`validate_trust_vc_request` is mode-aware at the pinned rev, so it no longer
demands a certificate per obligation of a discharge request (the adapter's
relaxation, `is_discharge_mode_certificate_rule`, now matches nothing).

Each request cites the POSTCONDITION alone. trust-ir refuses a discharge request
citing an obligation that is not sited in the requested function
(`TrustVcDischargeObligationNotSitedInFunction`), so the postcondition is sited
at the function's one `Return` terminator, which is where the lane checks it.
The def-site precondition stays in the module, unsited, and is ASSUMED; a
request cannot cite it.
