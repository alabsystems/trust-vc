::verus_builtin_macros::verus!{
pub trait Tr { }
spec fn id<A>(a: u8) -> u8 { a }
proof fn user() { assert(id::<(u8, u16)>(1) == 1); }
}
