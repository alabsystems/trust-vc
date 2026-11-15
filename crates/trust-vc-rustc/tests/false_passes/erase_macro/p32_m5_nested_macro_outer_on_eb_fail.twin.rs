::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
macro_rules! inner { () => { { let s = crate::S { x: 1 }; let a = s; } } }
#[verifier::external_body]
fn e() {
} macro_rules! outer { () => { inner!() } }
fn f() { outer!(); }
fn g() { assert(1 + 1 == 3); }
}
