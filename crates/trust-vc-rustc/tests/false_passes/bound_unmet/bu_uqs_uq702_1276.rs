verus!{
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for Z { }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Q { }
impl Q for B { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
} // verus!
