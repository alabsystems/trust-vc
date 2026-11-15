
verus!{
pub trait Tr { }
pub trait Q { }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub trait Sub: Q { }
pub struct Z { pub z: u8 }
pub proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
pub proof fn f1<X: Sub>(s: Z) { assert(<Z as U<X>>::mm(&s) == 2); }
pub proof fn f2<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
