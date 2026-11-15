verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for A { }
} // verus!
