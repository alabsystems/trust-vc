::verus_builtin_macros::verus!{
spec fn s() -> int {
    #[verifier::proof]
    let tracked x = 1int;
    x
}
}
