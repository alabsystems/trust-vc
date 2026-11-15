::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub trait T { fn m(&self, x: NC) -> u8; }
pub struct S {}
}
type Arg = NC;
::verus_builtin_macros::verus!{
fn user<A: T>(a: &A, x: Arg) -> (Arg, Arg) { (x, x) }
}
