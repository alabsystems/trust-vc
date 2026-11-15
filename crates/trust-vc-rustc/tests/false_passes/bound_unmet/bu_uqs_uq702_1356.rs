verus!{
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
