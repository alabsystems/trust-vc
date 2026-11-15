::verus_builtin_macros::verus!{
fn f() {}
pub struct P { pub p: &'static P }
pub struct Q { pub q: &'static Q }
fn user() { assert(1 + 1 == 2); }
}
