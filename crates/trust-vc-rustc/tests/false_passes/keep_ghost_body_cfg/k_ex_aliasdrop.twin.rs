::verus_builtin_macros::verus!{
pub struct T0 { pub y: u8 }
pub struct A { pub t: T0 }
pub struct B { pub t: T0 }
}
type X = B;
impl Drop for X { fn drop(&mut self) {} }
::verus_builtin_macros::verus!{
fn user(b: B) -> T0 { b.t }
}
