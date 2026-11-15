::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() { let x: u8; x = 1; x = 2; }
fn f() { assert(1 + 1 == 3); }
}
