::verus_builtin_macros::verus!{
pub struct G<T> { pub v: T }
pub struct NC { pub v: u8 }
}
type W = NC;
::verus_builtin_macros::verus!{
fn user(b: G<W>) -> (W, W) { (b.v, b.v) }
}
