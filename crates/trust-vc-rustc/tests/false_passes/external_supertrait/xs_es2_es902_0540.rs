
verus!{
#[verifier::external]
pub trait Sub<A>: Q<A> { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q<A> { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() != 2 { }
pub fn f1<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r != s.mm() { 2 }
pub proof fn f2<X: Sub<u8>>(s: S<X>) { assert(s.mm() != 2); }
} // verus!
