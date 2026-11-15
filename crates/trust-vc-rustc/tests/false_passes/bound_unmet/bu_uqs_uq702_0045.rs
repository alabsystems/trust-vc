verus!{
impl Tr for Z { }
pub struct A { pub a: u8 }
impl Tr for A { }
impl U for A {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Tr for B { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Q for B { }
pub struct B { pub b: u8 }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
