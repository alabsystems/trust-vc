pub trait Sub: Q + Tr { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) != 3 { }
} // verus!
