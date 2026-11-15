fn e() {
    #[macro_export]
    macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; } } }
}
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn f() -> (r: u8) ensures r == 1 { crate::mk!(); 1 }
fn g() { assert(1 + 1 == 3); }
}
