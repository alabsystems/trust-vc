
verus!{
pub trait Q { }
#[verifier::external]
pub trait Sub: Q { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub2;
pub open spec fn g0<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub2>(s: S<X>) ensures g0(s) == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
