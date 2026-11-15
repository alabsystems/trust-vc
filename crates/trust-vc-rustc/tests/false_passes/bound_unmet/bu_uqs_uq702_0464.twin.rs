verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
}
pub trait Q: Tr { } impl Tr for Z { } impl Q for Z { }
impl U for A {
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
impl Tr for A { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
} // verus!
