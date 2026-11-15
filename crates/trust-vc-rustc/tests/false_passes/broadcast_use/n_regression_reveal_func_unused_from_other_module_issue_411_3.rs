::verus_builtin_macros::verus!{
mod X {
    #[verifier(opaque)]
    pub open spec fn foo() -> bool { true }
}

proof fn test() {
    let _gv = { broadcast use X::foo; };
}
}
