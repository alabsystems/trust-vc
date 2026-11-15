verus!{
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
impl Q for B { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
