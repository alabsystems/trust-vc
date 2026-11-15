verus!{
impl Tr for Z { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
} // verus!
