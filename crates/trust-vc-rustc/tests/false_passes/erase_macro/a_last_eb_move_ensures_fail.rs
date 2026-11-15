::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
fn f() -> (r: u8) ensures r == 1 { mk!(); 1 }
fn g() { assert(1 + 1 == 3); }
}
