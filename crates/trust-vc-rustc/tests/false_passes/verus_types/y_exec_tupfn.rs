::verus_builtin_macros::verus!{
pub trait Tr { }
fn id<A>(a: u8) -> u8 { a }
fn user() { let x = id::<(u8, fn(u8) -> u8)>(1); }
}
