::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mk { () => { { let v: u8; let w = v; } } }
fn f() { mk!(); }
fn g() { assert(1 + 1 == 3); }
}
