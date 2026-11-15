pub trait Sub: Tr { }
verus!{
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() != 2); }
} // verus!
