::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
fn user(s: S) -> (S, S) { (s, s) }
}
impl Clone for S { fn clone(&self) -> Self { S { x: self.x } } }
#[cfg(not(verus_keep_ghost_body))]
impl Copy for S { }
