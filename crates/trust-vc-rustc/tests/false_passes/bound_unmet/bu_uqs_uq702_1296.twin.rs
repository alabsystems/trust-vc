verus!{
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for A { }
} // verus!
