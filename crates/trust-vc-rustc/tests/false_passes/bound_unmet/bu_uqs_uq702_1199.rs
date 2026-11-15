verus!{
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for B { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub struct B { pub b: u8 }
pub proof fn fA() { (A { a: 0 }).lm1(); }
} // verus!
