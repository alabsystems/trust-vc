pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() != 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub2 ensures s.mm() != 2 { }
pub open spec fn g2<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub2>(s: S<X>) ensures g2(s) != 2 { }
} // verus!
