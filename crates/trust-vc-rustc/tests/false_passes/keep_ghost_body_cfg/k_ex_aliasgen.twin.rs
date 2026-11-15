::verus_builtin_macros::verus!{
pub struct G<T> { pub v: T }
pub struct NC { pub v: u8 }
}
type W = u16;
impl Clone for G<W> { fn clone(&self) -> Self { G { v: self.v } } }
impl Copy for G<W> {}
::verus_builtin_macros::verus!{
fn user(b: G<u8>) -> (G<u8>, G<u8>) { (b, b) }
}
