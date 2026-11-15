::verus_builtin_macros::verus!{
fn test1() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let y = {
        let mut x = 5;
        #[verifier::proof_note("m")] x = 50;
        x
    };
    assert(x == 7);
    assert(y == 50);
}
}
