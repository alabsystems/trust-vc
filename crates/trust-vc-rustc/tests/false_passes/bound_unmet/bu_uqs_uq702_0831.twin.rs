verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for A { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub trait Q: Tr { }
impl Tr for B { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
} // verus!
