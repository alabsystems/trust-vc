
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
#[verifier::external]
pub use self::Tr as Sub;
pub struct S<X> { pub x: X }
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait V0 {
    proof fn f0<X: Sub>(s: Z) ensures <Z as U<X>>::mm(&s) == 2 { }
}
pub proof fn f1<X>(s: Z) where X: Sub ensures <Z as U<X>>::mm(&s) == 2 { }
} // verus!
