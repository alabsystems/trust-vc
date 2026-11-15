::verus_builtin_macros::verus!{
pub trait Tr { }
fn f<A>(a: A) where &'static mut u8: Sized { }
fn user() { f(1u8); }
}
