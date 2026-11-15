# Concrete typed quantifier controls

The six body fixtures retain the three source-only discriminator pairs from
`/tmp/trust-vc-quantifier-typed-template-independent1/probes/`, unchanged except
for the required outer `verus!` wrapper. The normal native common prelude is
supplied by the integration harness.

Pinned upstream Verus/Z3 already measured these exact bodies in
`/tmp/trust-vc-concrete-quantifier-oracle1/receipt.json`
(SHA256 `e5f8be5ada4d5e820f598b551f79f9fa45beef5944834a8e9b16f315b7b8dfce`).
Nat/Int identity, owned/reference decoration and negative-Int domain cases
are separate discriminators. A reference or Int seed does not license the
owned Nat existential; the verifier must report its exact assertion failure,
not an unsupported input or Unknown. The negative-domain case must not gain
Nat membership from an out-of-domain Int trigger.

The expected existential failures concern the original material-trigger
licensing behavior. Their existential formulas are mathematically true; do
not invent a witness or eager body unfolding to make these controls pass.

Native execution remains required at this source-only checkpoint. These
fixtures grant no new source, type, import or model permission.
