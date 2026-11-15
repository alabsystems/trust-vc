::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn test1() {
    let x: u64;
    x = 2;
    x = 3;
    assert(!(false)); // FAILS
}
}
