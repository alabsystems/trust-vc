::verus_builtin_macros::verus!{
pub trait Tr { }
pub struct S {}
impl S { fn id<A>(&self, a: u8) -> u8 { a } }
fn user(s: &S) { let x = s.id::<(u8, u16)>(1); }
}
