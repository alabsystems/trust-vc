::verus_builtin_macros::verus!{
struct A { v: u8 }
impl Drop for A {
    fn drop(&mut self)
        opens_invariants none

    {
    }
}
}
