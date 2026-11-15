::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() { fn mid() { fn inner(x: u8) -> u8 { x + 1 } } }
fn f() {}
}
