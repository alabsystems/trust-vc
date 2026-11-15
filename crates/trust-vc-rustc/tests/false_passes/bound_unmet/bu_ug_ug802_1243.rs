verus!{
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl Tr for u8 { }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Q requires self.mm() == 2 ensures true;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
} // verus!
