::verus_builtin_macros::verus!{
pub struct G<T> { pub v: T }
pub struct NC { pub v: u8 }
}
#[cfg(verus_keep_ghost_body)] type W = NC; #[cfg(not(verus_keep_ghost_body))] type W = u8;
::verus_builtin_macros::verus!{
fn user(b: G<W>) -> (W, W) { (b.v, b.v) }
}
