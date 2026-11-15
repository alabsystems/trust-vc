
verus!{
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
#[verifier::external]
pub trait Sub: Q { }
pub trait Tr { }
pub trait Q { }
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) == 2 { }
} // verus!
