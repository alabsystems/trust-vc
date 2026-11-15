verus!{
pub struct A { pub a: u8 } impl Q for A { }
impl Tr for A { }
pub trait U {
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
impl Tr for B { }
pub trait Q { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
} // verus!
