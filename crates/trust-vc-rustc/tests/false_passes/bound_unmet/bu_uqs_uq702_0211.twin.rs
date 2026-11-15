verus!{
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for A { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for Z { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
} // verus!
