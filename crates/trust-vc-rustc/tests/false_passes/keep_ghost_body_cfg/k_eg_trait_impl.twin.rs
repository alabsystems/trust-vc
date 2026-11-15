::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub trait T { fn m(&self, x: NC) -> u8; }
pub struct S {}
impl T for S {
    fn m(&self, x: NC) -> u8 { let p = x; let q = x; p.v }
}
}
