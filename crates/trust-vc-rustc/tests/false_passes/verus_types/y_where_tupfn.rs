::verus_builtin_macros::verus!{
pub trait Tr { }
fn f<A>(a: A) where (u8, fn(u8) -> u8): Sized { }
fn user() { f(1u8); }
}
