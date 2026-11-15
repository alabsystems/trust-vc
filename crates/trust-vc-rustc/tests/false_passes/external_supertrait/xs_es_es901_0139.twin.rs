
verus!{
pub trait Tr { }
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub use self::Q as Sub;
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
