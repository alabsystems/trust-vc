::verus_builtin_macros::verus!{
spec fn f<A>(a: A, x: u8) -> bool { recommends([x > 0]); recommends([x > 1]); true }
proof fn user() {{ assert(f(1u8, 1)); }}
}
