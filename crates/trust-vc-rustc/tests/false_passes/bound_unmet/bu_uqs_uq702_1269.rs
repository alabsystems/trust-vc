verus!{
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
pub trait Q { }
impl Q for B { }
impl Tr for Z { }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub proof fn fB() { (B { b: 0 }).lm0(); }
} // verus!
