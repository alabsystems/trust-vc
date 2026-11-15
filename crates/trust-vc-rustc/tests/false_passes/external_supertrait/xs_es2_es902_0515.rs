pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
