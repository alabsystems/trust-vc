::verus_builtin_macros::verus!{
pub struct S<T: Unpin> { pub a: T }
fn g<A: Unpin>(a: A) -> S<A> { S { a } }
fn f() { }
}
