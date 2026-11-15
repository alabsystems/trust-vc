verus!{
impl Q for A { }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for B { }
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
