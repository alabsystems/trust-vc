verus!{
pub struct B { pub b: u8 }
impl Tr for B { }
pub struct A { pub a: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl Q for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
impl Tr for A { }
pub trait Q: Tr { }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
} // verus!
