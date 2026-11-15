::verus_builtin_macros::verus!{
pub struct S<A> { pub a: A }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
