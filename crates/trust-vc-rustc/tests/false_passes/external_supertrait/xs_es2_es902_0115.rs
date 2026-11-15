pub trait Sub: Q { }
verus!{
pub trait Tr { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Q { }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub proof fn f0<X>(s: Z) where X: Sub ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub fn f2<X: Sub>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
