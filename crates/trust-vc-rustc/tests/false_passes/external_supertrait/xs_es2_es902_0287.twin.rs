
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
#[verifier::external]
pub use self::Q as Sub;
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
