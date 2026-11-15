verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
impl Q for A { }
pub trait Q { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
} // verus!
