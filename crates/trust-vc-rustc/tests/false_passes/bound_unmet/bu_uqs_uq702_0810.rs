verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z1() }
}
impl Tr for A { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
