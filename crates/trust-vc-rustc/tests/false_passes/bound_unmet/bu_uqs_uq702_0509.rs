verus!{
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for B { }
impl Tr for A { }
pub struct A { pub a: u8 }
} // verus!
