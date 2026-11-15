::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn h() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; } } }
#[verifier::external_body]
fn e() { mk!(); }
fn g() { assert(1 + 1 == 2); }
}
