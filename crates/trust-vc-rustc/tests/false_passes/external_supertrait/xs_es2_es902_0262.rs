pub trait Sub: Q + Tr { }
verus!{
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
