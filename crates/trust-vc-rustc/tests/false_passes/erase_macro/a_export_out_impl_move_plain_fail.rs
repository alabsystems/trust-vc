pub struct Q;
impl Q {
    fn e() {
        #[macro_export]
        macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
    }
}
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn f() { crate::mk!(); }
fn g() { assert(1 + 1 == 3); }
}
