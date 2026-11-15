pub use self::Tr as Sub;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X: Sub>(s: Z) { assert(<Z as U<X>>::mm(&s) == 2); }
} // verus!
