::verus_builtin_macros::verus!{
#[verifier::external_body]
uninterp spec fn f<A>(a: A) -> bool { recommends([true]); recommends([true]); true }
proof fn user() { assert(f(1u8) == f(1u8)); }
}
