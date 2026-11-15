::verus_builtin_macros::verus!{
spec fn s() -> int {
    #[verifier::spec]
    let tracked x = 1int;
    x
}
}
