pub trait Sub: Q { }
verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f<T: Sub>(z: Z) ensures <Z as U<T>>::mm(&z) == 2 { }
} // verus!
