verus!{
pub trait Q: Tr { } impl Tr for A { } impl Q for A { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Q for Z { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for B { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for B { }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for Z { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
pub proof fn fB() { (B { b: 0 }).lm0(); }
} // verus!
