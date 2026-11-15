pub trait Sub: Q { }
verus!{
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
}
} // verus!
