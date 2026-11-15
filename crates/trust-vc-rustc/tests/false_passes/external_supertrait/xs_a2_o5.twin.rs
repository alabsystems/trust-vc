pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub trait Q<A> { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
