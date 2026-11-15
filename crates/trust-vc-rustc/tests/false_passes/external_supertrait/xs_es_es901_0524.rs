pub trait Sub: Q + Tr { }
verus!{
pub struct Z { pub z: u8 }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait V0 {
    proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
}
pub proof fn f1<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
