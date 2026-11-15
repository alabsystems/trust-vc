verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
pub trait Q { }
} // verus!
