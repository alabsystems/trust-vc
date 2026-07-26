# TrustIr Adapter Fixtures

These JSON files are TrustVc-owned `TrustTrustIrAdapterRequest` goldens for the
runner and adapter boundary.

- `trust_x86_load_trust_ir_adapter_golden.json` is anchored to tRust
  `crates/trust-integration-tests/tests/binary_decompile_convert_llvm2_production_positive_golden.json`
  and carries its `trust_fixture_x86_load` symbol, TrustIr output digest, binary
  artifact digest, memory-fact count, and unsupported count.
- `trust_unresolved_indirect_branch_unsupported_trust_ir_adapter_golden.json` is
  anchored to tRust
  `crates/trust-integration-tests/tests/binary_unresolved_indirect_branch_golden.json`
  and must fail closed through `TrustUnsupportedTrustIrConstruct`.
- `trust_increment_contract_cfg_trust_ir_adapter_golden.json` is the tRust-native
  `TrustTrustIrAdapterRequest` golden from #2789/#2790. It covers first-class
  requires/ensures contract-frame evidence with `old(...)` and a typed CFG
  translation-validation obligation without using string-backed adapters.
