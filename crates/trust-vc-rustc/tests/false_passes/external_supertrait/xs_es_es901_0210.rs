pub trait Sub: Q { }
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub trait V1 {
    proof fn f1<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
}
} // verus!
