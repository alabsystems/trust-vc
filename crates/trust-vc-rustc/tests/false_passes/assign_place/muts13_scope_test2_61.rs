::verus_builtin_macros::verus!{
fn test1() {
    let mut x = 6;
    #[verifier::proof_note("m")] x = 60;
    let x = 7;
    {
        let mut x = 5;
        x = 50;
    }
    assert(x == 7);
}
}
