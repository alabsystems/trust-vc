pub use self::Tr as Sub;
verus!{
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) == 2 { }
pub trait V2 {
    proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
