verus!{
pub trait Tr { }
pub proof fn fZ() { (Z { z: 0 }).lm1(); }
impl Q for A { }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Q { }
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
} // verus!
