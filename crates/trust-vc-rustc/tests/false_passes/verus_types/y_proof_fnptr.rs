::verus_builtin_macros::verus!{
pub trait Tr { }
proof fn id<A>(a: u8) { }
proof fn user() { id::<fn()>(1); }
}
