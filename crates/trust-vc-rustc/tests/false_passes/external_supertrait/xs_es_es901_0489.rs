pub trait Sub: Tr { }
verus!{
pub struct S<X> { pub x: X }
pub trait Tr2 { }
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
impl<X: Tr> Tr2 for S<X> { }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() != 3); }
} // verus!
