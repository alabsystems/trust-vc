::verus_builtin_macros::verus!{
pub struct W<A> { pub a: u8, pub w: A }
pub struct P { pub p: u8 }
pub struct Q { pub q: W<&'static P> }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
