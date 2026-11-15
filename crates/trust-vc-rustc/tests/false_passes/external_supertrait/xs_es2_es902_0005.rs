pub trait Sub: Q { }
verus!{
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
