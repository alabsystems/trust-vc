verus!{
impl Q for Z { }
impl Tr for A { }
pub trait Q { }
impl Q for A { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct B { pub b: u8 }
} // verus!
