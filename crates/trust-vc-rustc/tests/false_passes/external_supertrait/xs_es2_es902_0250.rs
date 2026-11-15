pub trait Sub: Tr { }
verus!{
pub struct Z { pub z: u8 }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub trait V1 {
    proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
