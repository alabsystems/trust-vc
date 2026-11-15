::verus_builtin_macros::verus!{
pub struct W<A> { pub w: A, pub v: &'static u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
