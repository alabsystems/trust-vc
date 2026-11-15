verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for A { }
} // verus!
