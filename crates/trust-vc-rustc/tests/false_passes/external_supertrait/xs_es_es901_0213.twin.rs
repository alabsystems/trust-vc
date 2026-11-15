
verus!{
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
#[verifier::external]
pub use self::Q as Sub;
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
