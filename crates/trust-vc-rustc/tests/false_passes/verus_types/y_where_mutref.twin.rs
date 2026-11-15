::verus_builtin_macros::verus!{
pub trait Tr { }
fn f<A>(a: A){ }
fn user() { f(1u8); }
}
