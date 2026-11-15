::verus_builtin_macros::verus!{
pub struct P { pub p: &'static Q }
pub struct Q { pub q: &'static u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
