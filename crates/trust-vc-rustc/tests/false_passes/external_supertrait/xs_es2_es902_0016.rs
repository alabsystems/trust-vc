pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub trait Q { }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub fn f1<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
