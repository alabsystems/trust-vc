::verus_builtin_macros::verus!{
spec fn s() -> int {
    #[verifier::spec]
    let ghost x = 1int;
    x
}
}
