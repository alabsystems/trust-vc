pub use self::Tr as Sub;
verus!{
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub open spec fn g2<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub>(s: S<X>) ensures g2(s) == 2 { }
} // verus!
