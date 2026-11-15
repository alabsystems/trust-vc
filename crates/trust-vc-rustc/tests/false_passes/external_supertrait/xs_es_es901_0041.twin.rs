
verus!{
#[verifier::external]
pub use self::Tr as Sub;
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub proof fn f0<X>(s: Z) where X: Sub ensures <Z as U<X>>::mm(&s) != 2 { }
} // verus!
