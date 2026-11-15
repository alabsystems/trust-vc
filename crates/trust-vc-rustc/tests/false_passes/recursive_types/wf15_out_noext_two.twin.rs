::verus_builtin_macros::verus!{
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct P { pub p: &'static u8 }
pub struct Q { pub q: &'static Q }
