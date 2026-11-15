pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() != 3 { }
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
pub proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
} // verus!
