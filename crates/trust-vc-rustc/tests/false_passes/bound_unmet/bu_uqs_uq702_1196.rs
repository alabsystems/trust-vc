verus!{
impl Q for B { }
impl Tr for B { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
impl Q for A { }
} // verus!
