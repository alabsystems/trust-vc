fn e() {
} macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn f() { mk!(); }
proof fn g() { assume(true); }
}
