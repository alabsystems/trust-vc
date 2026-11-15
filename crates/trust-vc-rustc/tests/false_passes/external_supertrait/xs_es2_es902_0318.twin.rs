pub trait Sub: Tr { }
pub use self::Tr as Sub2;
verus!{
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
pub trait V2 {
    proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
