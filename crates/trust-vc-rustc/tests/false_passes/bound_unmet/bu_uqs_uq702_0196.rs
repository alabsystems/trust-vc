verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
impl Tr for Z { }
impl Tr for A { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for Z { }
} // verus!
