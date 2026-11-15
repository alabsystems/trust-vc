
verus!{
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub use self::Q as Sub;
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
