::verus_builtin_macros::verus!{
pub struct S0 { pub f0: &'static u8 }
fn ul() -> u8 { 1 }
fn id<B>(a: u8) -> u8 { a }
fn uc() { let x = id::<S0>(1); }
fn user() { assert(1 + 1 == 2); }
}
