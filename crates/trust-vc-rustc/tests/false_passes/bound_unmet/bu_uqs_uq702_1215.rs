verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for B {
    proof fn lm0(&self) { }
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Tr for A { }
impl Q for Z { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl Q for A { }
pub trait Q: Tr { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub proof fn fA() { (A { a: 0 }).lm0(); }
} // verus!
