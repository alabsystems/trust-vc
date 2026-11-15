pub trait Sub: Q + Tr { }
pub use self::Q as Sub2;
verus!{
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub open spec fn g0<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub2>(s: S<X>) ensures g0(s) != 2 { }
pub open spec fn g1<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub2>(s: S<X>) ensures g1(s) != 2 { }
} // verus!
