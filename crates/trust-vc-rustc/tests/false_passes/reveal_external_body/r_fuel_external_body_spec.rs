::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn s(a: bool) -> bool { a }
proof fn foo() { reveal_with_fuel(s, 1); }
}
