verus!{
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl Tr for B { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
}
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl Q for B { }
impl Q for A { }
} // verus!
