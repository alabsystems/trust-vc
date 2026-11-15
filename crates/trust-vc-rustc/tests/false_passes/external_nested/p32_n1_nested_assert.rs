::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() { fn inner() { assert(1 + 1 == 3); } }
fn f() {}
}
