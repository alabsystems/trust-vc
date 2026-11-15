verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Q for A { }
} // verus!
