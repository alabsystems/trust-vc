pub trait Sub: Q + Tr { }
pub use self::Q as Sub2;
verus!{
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f2<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
