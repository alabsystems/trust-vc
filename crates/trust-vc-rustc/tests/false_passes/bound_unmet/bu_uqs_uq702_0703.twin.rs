verus!{
pub struct B { pub b: u8 } impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for B { }
impl Q for B { }
} // verus!
