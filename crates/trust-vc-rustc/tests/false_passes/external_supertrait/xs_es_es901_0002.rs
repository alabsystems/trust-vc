
verus!{
#[verifier::external]
pub trait Sub: Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
#[verifier::external]
pub trait Sub2: Sub { }
pub trait Q { }
pub open spec fn g0<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub2>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
