verus!{
pub trait Tr { } impl Tr for u8 { } impl Q for u8 { }
pub struct S<X> { pub x: X }
impl U<u8> for Z {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
