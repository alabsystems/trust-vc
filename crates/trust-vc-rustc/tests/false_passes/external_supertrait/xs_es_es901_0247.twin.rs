pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() != 2 { }
}
} // verus!
