pub trait Sub: Q { }
verus!{
pub trait Q { }
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
} // verus!
