verus!{
impl Q for Z { }
impl Tr for A { }
pub struct B { pub b: u8 } impl Q for A { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub trait Tr { }
} // verus!
