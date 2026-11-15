verus!{
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
impl Q for u8 { }
pub trait Tr { }
pub trait Q { }
} // verus!
