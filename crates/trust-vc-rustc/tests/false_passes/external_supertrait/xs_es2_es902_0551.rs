pub trait Sub: Tr { }
pub trait Sub2: Sub { }
verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
