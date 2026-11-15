verus!{
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) { }
}
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub struct Z { pub z: u8 }
pub proof fn g<Y: Q + Tr>(s: S<Y>) where S<Y>: Q ensures s.mm() == 2 { s.lm0(); }
pub trait Tr { }
} // verus!
