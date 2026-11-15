verus!{
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
impl Tr for B { }
impl Q for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl Q for B { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
