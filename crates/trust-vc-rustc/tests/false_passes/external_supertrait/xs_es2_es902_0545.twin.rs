pub use self::Q as Sub;
verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub<u8>>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
