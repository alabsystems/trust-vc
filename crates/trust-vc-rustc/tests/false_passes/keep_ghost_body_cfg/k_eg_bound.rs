::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
}
#[cfg(verus_keep_ghost_body)] pub trait Dup {} #[cfg(not(verus_keep_ghost_body))] pub trait Dup: Copy {}
::verus_builtin_macros::verus!{
fn user<A: Dup>(a: A) -> (A, A) { (a, a) }
}
