verus!{
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl Tr for Z { }
pub trait Q: Tr { }
} // verus!
