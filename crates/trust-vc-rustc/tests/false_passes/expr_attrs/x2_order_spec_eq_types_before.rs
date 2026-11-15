::verus_builtin_macros::verus!{
spec fn s(x: int, y: bool) -> bool { let a = x == y; let b = #[verifier::no_such_attribute] 1int; a }
}
