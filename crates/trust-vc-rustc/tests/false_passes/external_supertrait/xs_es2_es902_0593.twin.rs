pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Q { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
