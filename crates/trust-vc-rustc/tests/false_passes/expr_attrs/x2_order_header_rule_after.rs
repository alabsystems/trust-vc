::verus_builtin_macros::verus!{
spec fn s(x: int) -> int requires #[verifier::no_such_attribute] x > 0 { x }
}
