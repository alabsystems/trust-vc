verus!{
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Tr for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
} // verus!
