::verus_builtin_macros::verus!{
#[verifier::external]
pub struct E(pub u8);
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<E>(1); }
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
