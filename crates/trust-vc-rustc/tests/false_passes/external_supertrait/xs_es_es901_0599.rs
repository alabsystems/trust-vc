pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
