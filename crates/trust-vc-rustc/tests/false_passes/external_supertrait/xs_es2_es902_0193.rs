
verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
#[verifier::external]
pub trait Sub: Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
