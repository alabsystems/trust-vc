verus!{
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for Z { }
pub proof fn g<Y: Q>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm1(); }
impl Q for Z { }
impl<X: Q> U for S<X> {
    proof fn lm0(&self) { }
    proof fn lm1(&self) where Self: Tr { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for u8 { }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr { }
}
} // verus!
