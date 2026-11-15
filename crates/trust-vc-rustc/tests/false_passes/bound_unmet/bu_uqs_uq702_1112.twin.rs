verus!{
pub trait Q { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
impl Tr for A { }
} // verus!
