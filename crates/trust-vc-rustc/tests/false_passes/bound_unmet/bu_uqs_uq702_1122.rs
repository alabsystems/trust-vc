verus!{
pub trait Q { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { assert(self.mm() == 2); }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
impl Q for Z { }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for A { }
pub trait Tr { }
impl Tr for A { }
} // verus!
