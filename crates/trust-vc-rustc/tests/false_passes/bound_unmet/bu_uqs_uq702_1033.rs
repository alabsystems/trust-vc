verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for B { }
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
pub struct A { pub a: u8 }
impl Tr for B { }
} // verus!
