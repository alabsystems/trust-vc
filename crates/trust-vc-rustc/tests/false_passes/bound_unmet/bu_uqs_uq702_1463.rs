verus!{
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
