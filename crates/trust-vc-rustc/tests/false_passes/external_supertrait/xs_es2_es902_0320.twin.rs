pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub open spec fn g0<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub2>(s: S<X>) ensures g0(s) == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
