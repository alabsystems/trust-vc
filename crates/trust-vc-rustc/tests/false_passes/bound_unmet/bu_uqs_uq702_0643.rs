verus!{
pub trait Q { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for A { }
pub struct A { pub a: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
} // verus!
