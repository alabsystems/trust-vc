
verus!{
#[verifier::external]
pub trait Sub: Q + Tr { }
#[verifier::external]
pub use self::Q as Sub2;
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait V0 {
    proof fn f0<X: Sub2>(s: Z) ensures <Z as U<X>>::mm(&s) != 2 { }
}
} // verus!
