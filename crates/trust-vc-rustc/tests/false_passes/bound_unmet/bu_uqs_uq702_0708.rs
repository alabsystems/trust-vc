verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for B { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Q for B { }
} // verus!
