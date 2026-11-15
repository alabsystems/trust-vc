verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct S<X> { pub x: X }
pub trait Q { }
impl Q for u8 { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for u8 { }
pub struct Z { pub z: u8 }
} // verus!
