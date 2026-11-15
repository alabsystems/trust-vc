::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
pub struct S {}
#[verifier::external]
pub struct E(pub u8);
fn id<A>(a: u8) -> u8 { a }
spec fn sid<A>(a: int) -> int { a }
proof fn pid<A>() { }
pub trait Tm { fn m(&self) -> u8; }
impl Tm for S { fn m(&self) -> u8 { id::<Option<u8>>(1) } }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
