verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl Q for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Tr for Z { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub trait Tr { }
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
