::verus_builtin_macros::verus!{
#[cfg_attr(not(verus_keep_ghost_body), derive(Clone, Copy))]
pub struct NC { pub v: u8 }
fn user(x: NC) -> (NC, NC) { (x, x) }
}
