::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external]
fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; } } }
fn f() { mk!(); }
proof fn g() { assume(true); }
}
