::verus_builtin_macros::verus!{
#[verifier::external]
mod m { pub struct E(pub u8); }
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<m::E>(1); }
fn user() { assert(1 + 1 == 2); }
}
pub trait Outer {}
