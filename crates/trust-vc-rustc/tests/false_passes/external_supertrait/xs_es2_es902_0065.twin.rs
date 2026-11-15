pub use self::Q as Sub;
verus!{
pub trait Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub trait Q { }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 2 { }
} // verus!
