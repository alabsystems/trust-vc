pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub fn f0<X: Sub>(s: Z) -> (r: u8) ensures r != <Z as U<X>>::mm(&s) { 2 }
pub proof fn f1<X>(s: Z) where X: Sub ensures <Z as U<X>>::mm(&s) != 2 { }
pub proof fn f2<X: Sub>(s: Z) { assert(<Z as U<X>>::mm(&s) != 2); }
} // verus!
