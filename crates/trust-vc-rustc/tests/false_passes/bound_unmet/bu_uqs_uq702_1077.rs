verus!{
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl Q for Z { }
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
impl Tr for Z { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub trait Tr { }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
} // verus!
