::verus_builtin_macros::verus!{
pub struct P {
    pub a: u8,
    pub p: &'static P,
}
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
