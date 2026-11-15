::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
pub trait Tr { fn m(&self); }
impl<T: Unpin> Tr for S<T> { fn m(&self) {} }
fn f(s: &S<u8>) { s.m(); }
}
