pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Tr { }
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
pub open spec fn g1<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub2>(s: S<X>) ensures g1(s) == 2 { }
pub proof fn f2<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
