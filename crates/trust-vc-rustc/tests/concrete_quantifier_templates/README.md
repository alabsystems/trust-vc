# Original concrete generic quantifier programs

The four `.rs` files are byte-identical copies of the complete actual source
files staged by `trust-vc-generic-composed-ed4baa1`. They are data fixtures for
the native integration target, which uses their unchanged macro body with the
ordinary checked-in `common` prelude. No assertion, type argument, trigger or
expected source-site verdict is changed.

The preserved current record extraction is
`/tmp/trust-vc-client-generic-composed-full1/quantifier-loss-records.json`
(SHA256 c6e349c040223420f4f8e9c063ad15af34ebc760f2fb07957568d314339762f9).
The complete historical successful source directories were not retained by the
old harness. Only the failed twin has directly retained old source bytes; all
four old/current harness binaries match. Do not describe the other three as a
direct old/current source-byte comparison.

The three positives must regain their original two proved sites. The absent
material-call case must retain one assertion failure on macro-body line 7;
its existential formula being mathematically satisfiable does not authorize
inventing a material seed, witness, eager unfolding or Nat membership fact.

These controls are prepared only at the source checkpoint. No native execution,
reference result or query/ABI footprint is claimed here.
