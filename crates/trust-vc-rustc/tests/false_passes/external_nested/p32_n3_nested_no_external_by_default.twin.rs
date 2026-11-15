::verus_builtin_macros::verus!{
#[verifier::verify]
fn e() { fn inner(x: u8) -> u8 { x + 1 } }
fn f() {}
}
