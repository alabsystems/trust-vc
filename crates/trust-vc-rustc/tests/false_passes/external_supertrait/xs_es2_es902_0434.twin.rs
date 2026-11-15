
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub struct S<X> { pub x: X }
pub trait Q { }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() != 3); }
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) != 3 { }
} // verus!
