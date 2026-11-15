::verus_builtin_macros::verus!{
spec fn s(x: int, y: bool) -> bool { let a = #[verifier::no_such_attribute] 1int; x == y }
}
