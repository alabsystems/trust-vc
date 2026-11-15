fn eo() {
    #[macro_export]
    macro_rules! mk { () => { { let s = crate::S { x: 1 }; let a = s; let b = s; } } }
}
::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() { crate::mk!(); }
fn g() { assert(1 + 1 == 3); }
}
