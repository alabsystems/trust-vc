
verus!{
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
#[verifier::external]
pub trait Sub: Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f2<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
