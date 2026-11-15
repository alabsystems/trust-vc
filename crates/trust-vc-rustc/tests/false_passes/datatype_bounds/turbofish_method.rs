::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn m<A>(&self, x: u8) -> u8 { x } }
fn f(s: &S) { let y = s.m::<fn()>(1); }
}
