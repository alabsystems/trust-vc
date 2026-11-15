::verus_builtin_macros::verus!{
pub trait T {
    fn f(&self) -> impl Sized;
}
fn user() { assert(1 + 1 == 2); }
}
