pub use self::Q as Sub;
verus!{
pub trait Q<A> { }
impl<T: Q<u8>> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub<u8>>(s: Z) { assert(<Z as U<X>>::mm(&s) == 2); }
} // verus!
