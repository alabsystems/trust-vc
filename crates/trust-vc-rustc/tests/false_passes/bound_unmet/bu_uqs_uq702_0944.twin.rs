verus!{
pub struct Z { pub z: u8 } impl Tr for A { } impl Q for A { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
} // verus!
