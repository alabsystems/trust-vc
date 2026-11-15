pub trait Sub: Q + Tr { }
pub trait Sub2: Sub { }
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub proof fn f0<X>(s: Z) where X: Sub2 ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
