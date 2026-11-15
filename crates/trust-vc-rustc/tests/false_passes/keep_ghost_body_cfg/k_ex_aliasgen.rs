::verus_builtin_macros::verus!{
pub struct G<T> { pub v: T }
pub struct NC { pub v: u8 }
}
#[cfg(verus_keep_ghost_body)] type W = u16; #[cfg(not(verus_keep_ghost_body))] type W = u8;
impl Clone for G<W> { fn clone(&self) -> Self { G { v: self.v } } }
impl Copy for G<W> {}
::verus_builtin_macros::verus!{
fn user(b: G<u8>) -> (G<u8>, G<u8>) { (b, b) }
}
