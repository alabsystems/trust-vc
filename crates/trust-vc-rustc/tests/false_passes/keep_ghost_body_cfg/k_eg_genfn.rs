::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
#[cfg(verus_keep_ghost_body)] fn user<A>(x: NC, a: A) -> u8 { let p = x; let q = x; p.v } #[cfg(not(verus_keep_ghost_body))] fn user<A>(x: NC, a: A) -> u8 { x.v }
}
