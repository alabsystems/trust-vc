pub use self::Tr as Sub;
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
