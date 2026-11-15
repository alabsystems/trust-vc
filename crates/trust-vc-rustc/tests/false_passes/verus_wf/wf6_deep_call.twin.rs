::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<T<u16>>(1); }
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
