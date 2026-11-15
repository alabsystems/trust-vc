verus!{
pub proof fn g<Y: Q + Tr>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm1(); }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub trait Q { }
impl Tr for Z { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2 ensures true;
}
impl Q for u8 { }
} // verus!
