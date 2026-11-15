::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { if x > 0 { #[verifier::no_such_attribute] x } else { 0 } }
}
