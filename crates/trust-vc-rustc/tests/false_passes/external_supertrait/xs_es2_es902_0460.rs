
verus!{
#[verifier::external]
pub trait Sub<A>: Q<A> { }
pub trait Q<A> { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub fn f0<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub<u8>> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
pub struct W2<X> { pub w: S<X> }
impl<X: Sub<u8>> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
