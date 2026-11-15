verus!{
impl Q for u8 { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
