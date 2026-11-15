pub trait Sub: Q + Tr { }
pub trait Sub2: Sub { }
verus!{
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub open spec fn g0<X: Sub2>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub2>(s: S<X>) ensures g0(s) == 2 { }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub2> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
pub trait V2 {
    proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
