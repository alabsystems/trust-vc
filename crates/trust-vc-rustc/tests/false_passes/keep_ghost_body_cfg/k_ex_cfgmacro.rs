#[cfg(verus_keep_ghost_body)] macro_rules! twice { ($x:ident) => { { let a = $x; let b = $x; a.v } } } #[cfg(not(verus_keep_ghost_body))] macro_rules! twice { ($x:ident) => { { $x.v } } }
::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
fn user(x: NC) -> u8 { twice!(x) }
}
