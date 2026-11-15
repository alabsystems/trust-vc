verus!{
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait Q { }
impl Q for B { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
} // verus!
