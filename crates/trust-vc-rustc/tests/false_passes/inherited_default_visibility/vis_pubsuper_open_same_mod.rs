::verus_builtin_macros::verus!{
pub mod m { use verus_builtin::*;
    pub(super) trait T { open spec fn d(&self) -> int { 1 } }
    pub struct S;
    impl T for S {}
}
}
