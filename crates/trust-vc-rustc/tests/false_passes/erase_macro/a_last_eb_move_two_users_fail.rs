::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
fn f() { mk!(); }
fn f2() { mk!(); }
fn g() { assert(1 + 1 == 3); }
}
