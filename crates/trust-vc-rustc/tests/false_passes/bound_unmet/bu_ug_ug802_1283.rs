verus!{
impl Tr for u8 { }
impl Q for u8 { }
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Tr for Z { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
impl<X> U for S<X> {
    proof fn lm0(&self) where Self: Tr { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn g<Y: Q>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { }
pub struct Z { pub z: u8 }
} // verus!
