::verus_builtin_macros::verus!{
pub mod m { use verus_builtin::*;
    pub(crate) trait T { open spec fn d(&self) -> int { 1 } }
    pub mod n { pub struct S; impl super::T for S {} }
}
}
