verus!{
pub struct A { pub a: u8 }
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for A { }
pub struct Z { pub z: u8 }
} // verus!
