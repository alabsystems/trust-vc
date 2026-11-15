verus!{
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub trait Q { }
pub trait Tr { }
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
} // verus!
