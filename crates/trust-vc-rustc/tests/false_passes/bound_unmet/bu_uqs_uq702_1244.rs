verus!{
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
} // verus!
