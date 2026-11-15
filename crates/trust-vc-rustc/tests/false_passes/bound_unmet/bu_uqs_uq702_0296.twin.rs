verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for Z { }
impl Tr for Z { }
pub struct B { pub b: u8 }
} // verus!
