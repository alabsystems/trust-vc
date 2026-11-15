::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
}
pub trait Dup {}
::verus_builtin_macros::verus!{
fn user<A: Dup>(a: A) -> (A, A) { (a, a) }
}
