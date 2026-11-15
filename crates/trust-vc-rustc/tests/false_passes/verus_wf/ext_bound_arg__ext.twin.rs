::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
pub struct S {}
pub trait Tr2 { }
pub trait Tg<A> { fn tg(&self) -> u8; }
pub trait Tr { fn tf(&self) -> u8; }

pub struct E(pub u8);
fn id<A>(a: u8) -> u8 { a }
spec fn sid<A>(a: int) -> int { a }
proof fn pid<A>() { }
impl S { fn m<A>(&self) -> u8 { 1 } }
fn g<A: Tg<E>>(a: u8) { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
