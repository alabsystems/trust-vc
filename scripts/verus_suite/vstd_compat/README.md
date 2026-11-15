# Pinned Verus library compatibility inputs

`a40d57c-trust29ebb-allocator-clone.patch` adapts the pinned Verus source
`a40d57c73650cd3648b09386bfdb96ab5c270626` to the actual allocator parameter
requirements of Trust `29ebb403de7a102850d6cb10a62d5cc3baf723ed`.

The original whole-module std+alloc declaration build failed with26 E0277
errors: BTreeMap/BTreeSet now require the real unsafe trait
`core::alloc::AllocatorClone`, whose supertraits are Allocator+Clone. The patch
replaces one import and36 allocator-A bounds in `std_specs/btree.rs` (21 map,
15 set). All other type/lifetime/where bounds, attributes, contracts, formulas,
bodies and modules remain unchanged. It grants no trait implementation and
adds no alias, shim, cfg exclusion or invented API. The extra `where A: Clone`
bound on BTreeSet::clear remains intact.

The JSON manifest pins the upstream/compiler identities and old/new file and
patch SHA256s. Apply only to the exact expected file hash in a separate owned
source view; reject a mismatched source or patch. The original archive/source
and measurement oracle must stay unchanged. Reproduce the source transform
with ordinary `git apply` in that separate exact source root, then require the
manifest's patched-file hash and a whole-tree comparison showing precisely the
one-file delta.

Build provenance must say **a40 + this explicit compatibility patch**, never
unmodified a40. Both Keep-body declaration analysis and ordinary macro Erase
compilation must use the same source identity. An Erase declaration artifact
proves no original body, contract or absence of headers; it cannot authorize
imports or verified-function counts. Authenticated mode/header/identity receipts
are a separate prerequisite. This patch is source preparation, not a claim that
the compatibility view has compiled or passed tests.
