::verus_builtin_macros::verus!{
spec fn s() -> int {
    #[verifier::proof]
    let ghost x = 1int;
    x
}
}
