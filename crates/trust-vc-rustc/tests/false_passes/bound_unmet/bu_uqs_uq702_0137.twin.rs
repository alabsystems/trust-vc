verus!{
pub struct Z { pub z: u8 } impl Q for A { }
impl Q for B { }
impl Q for Z { }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
