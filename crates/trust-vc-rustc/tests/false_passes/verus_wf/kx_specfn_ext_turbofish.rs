::verus_builtin_macros::verus!{
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<spec_fn(Option<u8>) -> bool>(1); }
fn user() { assert(1 + 1 == 2); }
}
pub trait Outer {}
