
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub use self::Q as Sub;
pub trait Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q<A> { }
pub trait V0 {
    proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
