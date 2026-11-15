::verus_builtin_macros::verus!{
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<u16>(1); }
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
