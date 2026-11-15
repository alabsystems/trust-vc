::verus_builtin_macros::verus!{
fn test1() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let x = {
        let mut x = 5;
        #[verifier::trigger] x = {let x = x + 50; x + 50};
        x
    };
    assert(x == 105);
}
}
