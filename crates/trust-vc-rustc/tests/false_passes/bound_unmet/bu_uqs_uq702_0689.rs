verus!{
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for B { }
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub trait Tr { }
impl Q for A { }
pub fn fA() { let _r = (A { a: 0 }).z1(); }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z1() }
}
} // verus!
