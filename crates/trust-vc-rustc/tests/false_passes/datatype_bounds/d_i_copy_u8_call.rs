::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
pub struct S<T> { pub a: T }
pub trait Tm { fn m(&self); }
impl<T: Copy> Tm for S<T> { fn m(&self) { } }
fn f(s: &S<u8>) { s.m(); }
}
