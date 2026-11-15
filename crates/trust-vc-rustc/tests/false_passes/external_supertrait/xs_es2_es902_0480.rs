pub trait Sub: Tr { }
verus!{
pub trait Tr { }
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait V0 {
    proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
}
pub trait V1 {
    proof fn f1<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
}
} // verus!
