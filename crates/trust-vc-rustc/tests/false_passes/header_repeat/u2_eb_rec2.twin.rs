::verus_builtin_macros::verus!{
#[verifier::external_body]
uninterp spec fn f() -> bool { recommends([true]); true }
proof fn user() { assert(f() == f()); }
}
