::verus_builtin_macros::verus!{
pub trait Tg<A> { }
pub struct S {}
impl<A> Tg<(A, Option<u8>)> for S { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
