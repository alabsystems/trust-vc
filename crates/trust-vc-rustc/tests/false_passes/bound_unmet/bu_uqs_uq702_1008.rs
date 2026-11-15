verus!{
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z0() }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
impl Q for A { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
pub trait Tr { }
impl Tr for B { }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
