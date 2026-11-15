pub trait Sub: Q + Tr { }
pub trait Sub2: Sub { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub fn f0<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
pub trait V2 {
    proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
