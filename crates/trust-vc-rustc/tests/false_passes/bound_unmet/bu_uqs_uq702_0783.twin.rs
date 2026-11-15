verus!{
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct A { pub a: u8 }
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for A { }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for A {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
impl Tr for A { }
} // verus!
