pub use self::Tr as Sub;
verus!{
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
