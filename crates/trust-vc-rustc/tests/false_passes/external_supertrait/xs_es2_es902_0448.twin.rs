
verus!{
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
} // verus!
