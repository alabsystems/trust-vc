# trust-ir body-lane fixtures

`guarded_checked_add_u8.json` is a serde-JSON `trust_ir::Module` for the
in-process body lane (`trust_vc_trust_engine::trust_ir_body`).

**Provenance — hand-built, NOT Trust-emitted.** It is the output of the test
builder in `tests/support/trust_ir_body_fixtures.rs`, which preserves historical
`crates/trust-ir-bridge/src/lower.rs` shapes (a
`requires` clause as `Const` + `ICmp` + `Assume`; a `CheckedBinaryOp` as
`Overflow` + `Undef Tuple` + two `InsertField`; a `Terminator::Assert` as
`ExtractField .1` + `Const Bool false` + `ICmp Eq Bool` + `Assert` + a sited
obligation + `Br`). It records what the lane accepts; it does not claim
agreement with the producer, and nothing here has been round-tripped through
Trust.

The bridge now uses complete `MakeAggregate` tuples instead of the legacy
`Undef` pack. `tests/trust_ir_body_aggregate.rs` checks that scalar-tuple
fragment with exact declaration order/types, module-as-written replay,
false claims and mutation/refusal controls. This JSON remains the legacy
havoc fixture; its bytes and interpretation are unchanged.

**This module is NOT executable as written.** The checked-op pack seeds its
tuple with `Inst::Undef`, and the pinned reference interpreter calls executing
one at a tuple type undefined behaviour (trust-ir@4f09dab8 `interpret.rs:1194`
-> `scalar_poison`: aggregate poison is unmodelled) — so on the
module as written, no input reaches the `Assert` at all. The lane decides the
HAVOC reading instead (an admitted `Undef` denotes a fresh unconstrained
value), which is the over-approximation trust-ir's own `FreshSymbolicHavoc`
doc sanctions and which the lane keeps sound structurally by refusing every
read of a field no `InsertField` wrote. Verdicts about this fixture therefore
carry `BodyReading::HavocInstantiatedUndef`, and so does every witness
replayed on it. `tests/trust_ir_body_discharge.rs::the_real_checked_op_pack_is_undefined_behaviour_under_the_pinned_interpreter`
pins the measurement; see the `trust_ir_body` module doc for the full
argument.

**Pin.** trust-ir `0.14.0@bd313b4fbfae2c2826bade463e23224f1df9a61a`
(binary format v70, bundle schema v8); the builder reproduces this file byte
for byte there. No completeness or bound-certificate claim is added. The
lane refuses a `Drop` and an `ArraySplat` by name, any `Uninit` or
`Splat` constant, a sited `Assert` or one whose kind carries operands, and
the unwinding and no-unwind twins (`AssertInvoke`, `CallCannotUnwind`,
`CallIndirectCannotUnwind`, `DropInvoke`, `InvokeIndirect`), the six tensor
operations (`TensorContract`, `TensorMap`, `TensorReduce`, `TensorView`,
`TensorGather`, `TensorScatter`), any `Ty::Tensor` and `TensorBlob` constant,
and a module carrying `Module.blobs`, as outside v0. The
JSON encoding is serde's, which is NOT a stable wire format: regenerate on
every trust-ir pin move with

```sh
TRUST_VC_REGEN_TRUST_IR_BODY_FIXTURES=1 \
  targo --unverified test -p trust-vc-trust-engine --test trust_ir_body_discharge -- \
  the_checked_in_fixture_matches_the_builder
```

and review the diff — a changed shape is a signal, not noise. The check reads
the file through `include_str!`, so regeneration takes two runs: the first
writes the file, the second compares against it.

**Still owed.** Add `trust_ir_build::validate_module` as a dev-dependency
check over this fixture, so the lane's own structural check
(`src/trust_ir_body/check.rs`) is measured against upstream's validator rather
than only against itself. `trust-ir-build` is already a production dependency
(coverage admission) at the cohort's single TrustIR identity, so nothing
blocks it.
