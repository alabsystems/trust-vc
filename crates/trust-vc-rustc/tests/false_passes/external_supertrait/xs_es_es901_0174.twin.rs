
verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub fn f1<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
