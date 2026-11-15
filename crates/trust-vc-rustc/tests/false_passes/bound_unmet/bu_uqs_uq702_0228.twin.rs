verus!{
pub trait Tr { } impl Tr for A { } impl Q for A { }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
} // verus!
