::verus_builtin_macros::verus!{
pub struct P { pub p: (&'static Q, &'static P) }
pub struct Q { pub q: &'static Q }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
