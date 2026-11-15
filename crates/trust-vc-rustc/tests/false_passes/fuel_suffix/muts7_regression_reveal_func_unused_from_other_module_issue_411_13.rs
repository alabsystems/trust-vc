::verus_builtin_macros::verus!{
mod X {
    #[verifier(opaque)]
    pub open spec fn foo() -> bool { true }
}

proof fn test() {
    reveal_with_fuel(X::foo, 1u32);
}
}
