::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
#[cfg(verus_keep_ghost_body)] fn user(x: NC) -> u8 { let a = x; let b = x; a.v } #[cfg(not(verus_keep_ghost_body))] fn user(x: NC) -> u8 { x.v }
}
