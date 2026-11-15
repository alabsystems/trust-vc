pub use self::Q as Sub;
verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub trait V1 {
    proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f2<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
