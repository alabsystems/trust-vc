verus!{
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for Z { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Tr { }
pub trait Q { }
} // verus!
