
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Q<A> { }
impl<X: Q<u8>> Tr for S<X> { }
pub struct Z { pub z: u8 }
#[verifier::external]
pub use self::Q as Sub;
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait V0 {
    proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f1<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
} // verus!
