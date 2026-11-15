::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
fn f() { mk!(); }
fn h(a: u8) requires a > 5 {}
fn g() { h(1); }
}
