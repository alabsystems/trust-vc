::verus_builtin_macros::verus!{
fn test1() {
    let x: u64;
    #[allow(unused_assignments)]
    #[verifier::proof_note("m")] x = 23;
}
}
