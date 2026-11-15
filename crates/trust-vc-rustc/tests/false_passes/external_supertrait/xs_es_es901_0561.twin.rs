pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
