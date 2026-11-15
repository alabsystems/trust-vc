verus!{
impl Tr for B { }
impl Q for B { }
pub trait Tr { }
impl Q for Z { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q { }
impl Q for A { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
