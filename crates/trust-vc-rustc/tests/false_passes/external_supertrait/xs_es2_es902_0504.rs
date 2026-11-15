pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub proof fn f0<X: Sub2>(s: S<X>) { assert(s.mm() != 2); }
} // verus!
