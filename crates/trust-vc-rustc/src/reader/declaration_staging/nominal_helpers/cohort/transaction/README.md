# Explicit genuine transaction controls

These four ignored unit tests run the real fresh builtin constructor and full
Erase/load/Keep producer. They do not reconstruct capabilities from old reports.
Each test needs a separate admitted standalone process, an exact test-name filter,
`--exact --ignored --test-threads=1`, and optional `--nocapture`. The code refuses
any broader test invocation. No environment variable is changed in the process.

Before starting the process, set `VSTD_KIND=IsVstd` and set
`TRUST_VC_HELPER_TRANSACTION_FIXTURE` to one absolute canonical fixture JSON path.
The controller must bind the actual executable/compiler/source/private AY inputs,
the fixture and every request hash, and new absent output/builtin directories.
Use the normal genuine Trust loader and build-slot admission. These tests have
not been compiled or run at this source checkpoint.

The fixture schema is `trust-vc.helper-transaction-test-fixture@1`. Its `cases`
object contains `reversible`, `drop`, `diagnostics`, and `unwind`. Each case has
`request: {path, sha256}` selecting an exact normal schema-2 staging request, and
`report` selecting a fresh report file outside the approved source graph. Only
`reversible` also has `alternate_inputs_request: {path, sha256}`. That request
uses the same source recipe but distinct absent output/builtin directories; it
runs another real builtin construction to obtain different genuine Inputs.
Every individual producer invocation needs its own request/output roots.

The four test names are:

- `genuine_helper_transaction_associations_and_owned_bytes`
- `genuine_helper_transaction_drop_without_commit`
- `genuine_helper_transaction_diagnostics_revoke_commit`
- `genuine_helper_transaction_unwind_without_commit`

They live under
`reader::declaration_staging::nominal_helpers::cohort::transaction::fixture::tests`.

The reversible control requires at least two actual pending nominal facts. It
recaptures native policy/WF/Fields/helper facts and their source/builtin joins,
checks wrong Inputs/Metadata association, distinct capture Arcs, mixed pending
and owned scopes, and a wrong actual map owner. It changes only the completed
owned builder script and one owned archive copy, requires finalization to reject,
restores the exact bytes, and checks full revalidation. The original pending map
then follows the unchanged normal finalizer and StagedLibrary construction.
Zero-helper nominal facts exercise transaction ownership but are not a positive
qualification of generated getter semantics.

The drop test checks that an uncommitted callback result does not become a
StagedLibrary; its runtime sentinel is weaker than private type/conversion rules.
The diagnostic test emits a real native error and never cancels it. The unwind
test accepts only its private typed payload after the compiler has unwound, then
ends without another native query or compiler invocation. Other panic payloads
are rethrown. No generic compiler failure or timeout qualifies either case.

The private Probe, fields, selector and producer argument exist only under
`cfg(test)`. Release signatures/layout and ordinary product import behavior are
unchanged. Output JSON is test evidence and has no authority constructor.
