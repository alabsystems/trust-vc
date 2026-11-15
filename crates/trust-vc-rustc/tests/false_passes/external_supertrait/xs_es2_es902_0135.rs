
verus!{
#[verifier::external]
pub trait Sub: Tr { }
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
pub fn f0<X: Sub>(s: Z) -> (r: u8) ensures r != <Z as U<X>>::mm(&s) { 2 }
} // verus!
