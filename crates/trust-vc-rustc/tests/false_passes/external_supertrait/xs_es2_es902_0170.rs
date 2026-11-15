pub trait Sub: Q + Tr { }
pub trait Sub2: Sub { }
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
pub proof fn f2<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
