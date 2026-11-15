
verus!{
pub struct Z { pub z: u8 }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
#[verifier::external]
pub trait Sub<A>: Q<A> { }
pub struct S<X> { pub x: X }
pub trait Q<A> { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub proof fn f0<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
pub open spec fn g1<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub<u8>>(s: S<X>) ensures g1(s) == 2 { }
pub fn f2<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
