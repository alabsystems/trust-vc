verus!{
pub trait Q { } impl Q for Z { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for A { }
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for A { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for B { }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
