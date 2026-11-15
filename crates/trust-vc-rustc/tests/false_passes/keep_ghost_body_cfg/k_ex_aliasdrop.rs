::verus_builtin_macros::verus!{
pub struct T0 { pub y: u8 }
pub struct A { pub t: T0 }
pub struct B { pub t: T0 }
}
#[cfg(verus_keep_ghost_body)] type X = B; #[cfg(not(verus_keep_ghost_body))] type X = A;
impl Drop for X { fn drop(&mut self) {} }
::verus_builtin_macros::verus!{
fn user(b: B) -> T0 { b.t }
}
