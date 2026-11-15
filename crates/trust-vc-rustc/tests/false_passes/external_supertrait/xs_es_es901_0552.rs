pub trait Sub: Tr { }
verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Tr { }
pub proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) != 2 { }
pub proof fn f1<X: Sub>(s: Z) { assert(<Z as U<X>>::mm(&s) != 2); }
pub fn f2<X: Sub>(s: Z) -> (r: u8) ensures r != <Z as U<X>>::mm(&s) { 2 }
} // verus!
