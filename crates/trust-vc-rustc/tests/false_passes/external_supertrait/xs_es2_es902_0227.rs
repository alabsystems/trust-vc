pub trait Sub: Tr { }
pub trait Sub2: Sub { }
verus!{
pub trait Tr { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
