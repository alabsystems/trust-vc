
verus!{
pub trait Q<A> { }
pub struct S<X> { pub x: X }
#[verifier::external]
pub trait Sub<A>: Q<A> { }
pub trait Tr { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
impl<T: Q<u8>> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X>(s: Z) where X: Sub<u8> ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub<u8>>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub fn f2<X: Sub<u8>>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
