
verus!{
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub trait V2 {
    proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
