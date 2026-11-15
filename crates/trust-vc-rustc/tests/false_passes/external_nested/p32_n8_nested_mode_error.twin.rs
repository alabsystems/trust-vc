::verus_builtin_macros::verus!{
spec fn s() -> int { 1 }
#[verifier::verify]
fn e() { fn inner() -> u8 { let x = s(); 1 } }
fn f() {}
}
