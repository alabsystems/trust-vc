
verus!{
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
#[verifier::external]
pub trait Sub: Q { }
#[verifier::external]
pub use self::Q as Sub2;
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
