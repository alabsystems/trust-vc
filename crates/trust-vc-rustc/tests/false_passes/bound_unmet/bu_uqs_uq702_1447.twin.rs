verus!{
impl Tr for A { }
pub proof fn fA() { (A { a: 0 }).lm1(); }
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q { }
pub struct A { pub a: u8 }
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
    open spec fn mm(&self) -> u8 { 2 }
}
} // verus!
