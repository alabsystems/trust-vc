pub trait Sub<A>: Q<A> { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
impl<T: Q<u8>> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub fn f0<X: Sub<u8>>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
