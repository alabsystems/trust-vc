pub trait Sub: Q + Tr { }
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub open spec fn g2<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub>(s: S<X>) ensures g2(s) == 2 { }
} // verus!
