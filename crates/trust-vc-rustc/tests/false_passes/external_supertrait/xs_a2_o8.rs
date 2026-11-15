pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub open spec fn g<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f<X: Sub>(s: S<X>) ensures g(s) == 2 { }
} // verus!
