
verus!{
pub trait Q<A> { }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub struct S<X> { pub x: X }
pub proof fn f0<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
} // verus!
