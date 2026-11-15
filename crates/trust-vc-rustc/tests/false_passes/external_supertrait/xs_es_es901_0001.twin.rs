pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q<A> { }
impl<X: Q<u8>> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub<u8> ensures s.mm() != 3 { }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub<u8>> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() != 3 { }
}
} // verus!
