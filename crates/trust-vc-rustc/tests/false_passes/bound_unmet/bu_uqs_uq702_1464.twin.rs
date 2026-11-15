verus!{
pub trait Tr { } impl Tr for A { } impl Q for A { }
impl Tr for Z { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
