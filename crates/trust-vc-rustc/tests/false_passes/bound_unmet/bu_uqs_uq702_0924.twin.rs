verus!{
impl Q for Z { }
pub trait Tr { } impl Tr for Z { }
impl Tr for A { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
} // verus!
