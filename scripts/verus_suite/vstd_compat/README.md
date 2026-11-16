# Pinned Verus library compatibility inputs

`a40d57c-trust82bb867-allocator-clone.{json,patch}` records the same source
adaptation for actual Trust `82bb867eddb94599f68194f701c766f2b6f5a02f`
(installed build 20882). A fresh, complete A40 source export was checked against
every Git blob. Its manifest SHA256 is
`8feafeb5b8901043b90b8b51b7853f8a4832d44f2c596865b68badeea618046b`.
The unmodified whole-module std+alloc build with this compiler again failed
with exactly 26 E0277 errors requiring `AllocatorClone`. The current recipe
binds the actual compiler, original file and patched file; it does not reuse
the historical SDK manifest identity or authorize an imported contract.
The complete patched std+alloc vstd then compiled successfully with current
Trust as an ordinary macro-Erase-body Rust library. This establishes source
compatibility, not verified proof bodies, a vstd export or imported authority.

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
are a separate prerequisite. A recipe alone is source preparation and establishes
neither a successful build nor passing verification tests.
