pub trait Sub: Tr { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub trait V2 {
    proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
