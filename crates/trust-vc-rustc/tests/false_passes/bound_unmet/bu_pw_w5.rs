verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z(&self) -> (r: u8) where Self: Tr requires self.mm() == 2 ensures r == 2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z(&self) -> (r: u8) { 2 }
}
pub fn g<Y: Q>(s: S<Y>) -> (r: u8) ensures r == 2 { s.z() }
} // verus!
