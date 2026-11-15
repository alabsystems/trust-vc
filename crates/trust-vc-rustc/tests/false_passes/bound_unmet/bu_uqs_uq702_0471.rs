verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Q for B { }
impl Tr for B { }
impl Tr for A { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
impl Tr for Z { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
