verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) where T: Tr ensures self.mm() == 2;
}
impl<X, T> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) { }
}
} // verus!
