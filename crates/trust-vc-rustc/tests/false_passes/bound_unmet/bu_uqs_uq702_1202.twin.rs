verus!{
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
