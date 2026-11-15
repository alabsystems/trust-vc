::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub trait T { fn m(&self, x: NC) -> u8; }
pub struct S {}
impl T for S {
    #[cfg(verus_keep_ghost_body)] fn m(&self, x: NC) -> u8 { let p = x; let q = x; p.v } #[cfg(not(verus_keep_ghost_body))] fn m(&self, x: NC) -> u8 { x.v }
}
}
