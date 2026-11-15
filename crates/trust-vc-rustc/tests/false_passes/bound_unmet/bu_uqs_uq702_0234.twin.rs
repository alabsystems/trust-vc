verus!{
pub trait Q { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
} // verus!
