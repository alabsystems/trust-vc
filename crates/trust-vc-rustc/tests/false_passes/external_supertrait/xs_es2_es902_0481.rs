pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
pub proof fn f1<X: Sub2>(s: S<X>) { assert(s.mm() != 3); }
} // verus!
