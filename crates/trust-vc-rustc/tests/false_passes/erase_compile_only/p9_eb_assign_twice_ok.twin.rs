::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() { let x: u8; x = 1; }
fn f() { assert(1 + 1 == 2); }
}
