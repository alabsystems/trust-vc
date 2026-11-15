verus!{
impl U for B {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Q for Z { }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
impl Tr for Z { }
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q { }
pub trait Tr { }
} // verus!
