::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub struct H { #[cfg(verus_keep_ghost_body)] pub f: NC, #[cfg(not(verus_keep_ghost_body))] pub f: u8 }
fn user(h: H) -> bool { let a = h.f; let b = h.f; true }
}
