verus!{
impl Q for B { }
impl U for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
impl Tr for A { }
impl Tr for B { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Tr for Z { }
impl Q for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
} // verus!
