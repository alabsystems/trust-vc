pub trait Sub<A>: Q<A> { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q<A> { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q<u8>> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub<u8>>(s: Z) { assert(<Z as U<X>>::mm(&s) == 2); }
} // verus!
