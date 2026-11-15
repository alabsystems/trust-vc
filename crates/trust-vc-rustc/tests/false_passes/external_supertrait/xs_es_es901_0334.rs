pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
