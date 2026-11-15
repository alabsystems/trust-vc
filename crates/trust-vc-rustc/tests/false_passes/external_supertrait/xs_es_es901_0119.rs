pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub proof fn f0<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) != 3 { }
pub proof fn f1<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) != 3 { }
} // verus!
