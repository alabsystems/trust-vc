pub trait Sub: Q { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub proof fn f0<X>(s: Z) where X: Sub ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub>(s: Z) { assert(<Z as U<X>>::mm(&s) == 2); }
} // verus!
