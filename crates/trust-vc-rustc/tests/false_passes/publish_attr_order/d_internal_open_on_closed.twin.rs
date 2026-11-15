::verus_builtin_macros::verus!{
pub mod m { use verus_builtin::*;
    #[verus::internal(open)]
    pub open spec fn s() -> int { 2 }
}
proof fn user() { assert(m::s() == 2); }
}
