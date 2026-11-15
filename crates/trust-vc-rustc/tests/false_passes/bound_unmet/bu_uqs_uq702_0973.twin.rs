verus!{
pub trait Q: Tr { }
pub trait Tr { }
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub struct A { pub a: u8 }
impl U for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
