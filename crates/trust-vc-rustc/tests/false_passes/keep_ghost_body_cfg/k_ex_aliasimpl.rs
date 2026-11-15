::verus_builtin_macros::verus!{
pub struct A { pub v: u8 }
pub struct B { pub v: u8 }
}
#[cfg(verus_keep_ghost_body)] type X = A; #[cfg(not(verus_keep_ghost_body))] type X = B;
impl Clone for X { fn clone(&self) -> Self { X { v: self.v } } }
impl Copy for X {}
::verus_builtin_macros::verus!{
fn user(b: B) -> (B, B) { (b, b) }
}
