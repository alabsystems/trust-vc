pub use self::Tr as Sub;
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Tr2 { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
impl<X: Tr> Tr2 for S<X> { }
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub fn f1<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
