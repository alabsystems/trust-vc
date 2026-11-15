verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
pub trait Q { }
pub trait Tr { }
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
