::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub trait T { fn m(&self, x: NC) -> u8; }
pub struct S {}
}
#[cfg(verus_keep_ghost_body)] type Arg = NC; #[cfg(not(verus_keep_ghost_body))] type Arg = u8;
::verus_builtin_macros::verus!{
fn user<A: T>(a: &A, x: Arg) -> (Arg, Arg) { (x, x) }
}
