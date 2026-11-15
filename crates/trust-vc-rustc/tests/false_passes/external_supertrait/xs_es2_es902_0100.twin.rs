
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
#[verifier::external]
pub use self::Q as Sub;
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) == 2 { }
pub trait V2 {
    proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
