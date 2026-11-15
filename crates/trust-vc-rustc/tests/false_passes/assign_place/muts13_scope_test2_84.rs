::verus_builtin_macros::verus!{
fn test1() {
    let mut x = 6;
    x = 60;
    let x = 7;
    {
        let mut x = 5;
        #[verifier::trigger] x = 50;
    }
    assert(x == 7);
}
}
