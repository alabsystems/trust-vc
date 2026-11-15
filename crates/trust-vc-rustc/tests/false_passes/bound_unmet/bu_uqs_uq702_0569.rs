verus!{
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl Tr for A { }
impl Q for B { }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for B { }
} // verus!
