fn e() {
    #[macro_export]
    macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; } } }
}
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn f() { crate::mk!(); }
fn h(a: u8) requires a > 5 {}
fn g() { h(1); }
}
