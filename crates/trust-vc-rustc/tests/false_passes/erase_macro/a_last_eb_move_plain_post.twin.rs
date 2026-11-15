::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; } } }
fn f() { mk!(); }
fn g() -> (r: u8) ensures r == 2 { 1 }
}
