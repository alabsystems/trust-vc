::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
fn f() { mk!(); }
fn g() -> (r: u8) ensures r == 2 { 1 }
}
