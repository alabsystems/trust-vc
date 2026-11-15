pub trait Sub<A>: Q<A> { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct S<X> { pub x: X }
pub trait Q<A> { }
impl<T: Q<u8>> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub<u8>>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub<u8>>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
