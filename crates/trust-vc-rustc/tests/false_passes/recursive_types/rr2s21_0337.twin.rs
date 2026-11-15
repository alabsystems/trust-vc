::verus_builtin_macros::verus!{
pub struct S0(pub i32, pub int, &'static u8);
fn id<B>(a: u8) -> u8 { a }
fn uc() { let x = id::<S0>(1); }
fn user() { assert(1 + 1 == 2); }
}
