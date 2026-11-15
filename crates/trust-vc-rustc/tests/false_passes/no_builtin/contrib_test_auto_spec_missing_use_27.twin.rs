use verus_builtin::*; ::verus_builtin_macros::verus!{

#[verifier::external] fn foo(x: u32) -> u32 {
    x / 2
}
}
