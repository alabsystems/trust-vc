pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q<u8>> Tr for S<X> { }
pub trait Q<A> { }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub fn f0<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r != s.mm() { 3 }
} // verus!
