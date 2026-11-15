pub use self::Q as Sub;
verus!{
pub trait Q<A> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q<u8>> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait V0 {
    proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
