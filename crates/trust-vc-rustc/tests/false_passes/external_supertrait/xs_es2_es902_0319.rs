pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub proof fn f0<X>(s: Z) where X: Sub2 ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
