::verus_builtin_macros::verus!{
pub trait T {
    fn f(&self) -> u8;
}
fn user() { assert(1 + 1 == 2); }
}
