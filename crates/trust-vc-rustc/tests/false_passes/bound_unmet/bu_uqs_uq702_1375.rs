verus!{
impl Q for A { }
impl U<B> for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { assert(self.mm() == 2); }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn rq1(&self) where T: Tr requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub trait Tr { }
impl U<A> for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { assert(self.mm() == 2); }
}
impl Tr for A { }
} // verus!
