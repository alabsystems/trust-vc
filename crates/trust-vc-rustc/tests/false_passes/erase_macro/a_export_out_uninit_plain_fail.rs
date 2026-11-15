fn e() {
    #[macro_export]
    macro_rules! mk { () => { { let v: u8; let w = v; } } }
}
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn f() { crate::mk!(); }
fn g() { assert(1 + 1 == 3); }
}
