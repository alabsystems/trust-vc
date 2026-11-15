verus!{
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub trait Tr { }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub struct A { pub a: u8 }
impl Tr for A { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
} // verus!
