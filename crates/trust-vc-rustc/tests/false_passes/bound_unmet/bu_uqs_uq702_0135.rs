verus!{
pub trait Tr { }
pub proof fn fA() { (A { a: 0 }).lm1(); }
impl Tr for Z { }
pub trait Q: Tr { }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
impl Q for Z { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
} // verus!
