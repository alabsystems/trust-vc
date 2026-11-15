verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for Z { }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for A { }
pub trait Q { }
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl Tr for B { }
} // verus!
