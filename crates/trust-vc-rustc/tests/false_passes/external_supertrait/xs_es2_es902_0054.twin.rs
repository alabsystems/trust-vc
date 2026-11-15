pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q> Tr for S<X> { }
pub fn f0<X: Sub2>(s: S<X>) -> (r: u8) ensures r != s.mm() { 3 }
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
pub open spec fn g2<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub2>(s: S<X>) ensures g2(s) != 3 { }
} // verus!
