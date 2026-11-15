pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) == 2 { }
} // verus!
