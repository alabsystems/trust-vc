verus!{
pub struct A { pub a: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl Q for Z { }
impl Tr for Z { }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
} // verus!
