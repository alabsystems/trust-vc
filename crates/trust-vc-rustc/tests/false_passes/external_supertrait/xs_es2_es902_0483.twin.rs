pub use self::Q as Sub;
verus!{
pub trait Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() != 3); }
} // verus!
