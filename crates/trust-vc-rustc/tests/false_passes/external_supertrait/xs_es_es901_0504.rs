pub trait Sub: Tr { }
verus!{
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
} // verus!
