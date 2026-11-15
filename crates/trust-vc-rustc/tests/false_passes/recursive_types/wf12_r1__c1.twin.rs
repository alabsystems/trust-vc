::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static u8 }
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<R>(1); }
fn user() { assert(1 + 1 == 2); }
}
