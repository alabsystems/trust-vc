pub use self::Tr as Sub;
verus!{
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait Tr { }
pub fn f0<X: Sub>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
