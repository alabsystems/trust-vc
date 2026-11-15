pub trait Sub: Tr { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) != 3 { }
pub proof fn f1<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) != 3 { }
pub proof fn f2<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) != 3 { }
} // verus!
