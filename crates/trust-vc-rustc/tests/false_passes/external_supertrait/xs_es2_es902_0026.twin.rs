pub use self::Tr as Sub;
verus!{
pub trait Tr2 { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub trait Q { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
impl<X: Tr> Tr2 for S<X> { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
