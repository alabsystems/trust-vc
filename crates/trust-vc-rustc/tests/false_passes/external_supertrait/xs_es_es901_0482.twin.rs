
verus!{
#[verifier::external]
pub trait Sub: Q { }
#[verifier::external]
pub use self::Q as Sub2;
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() != 2 { }
} // verus!
