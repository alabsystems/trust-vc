::verus_builtin_macros::verus!{
struct S { x: u8 }
#[verifier::external_body]
fn e() { fn inner() { } }
fn f() { assert(1 + 1 == 2); }
}
