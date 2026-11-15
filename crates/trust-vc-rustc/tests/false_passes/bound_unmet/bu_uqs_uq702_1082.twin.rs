verus!{
pub struct Z { pub z: u8 } impl Tr for A { } impl Q for A { }
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
} // verus!
