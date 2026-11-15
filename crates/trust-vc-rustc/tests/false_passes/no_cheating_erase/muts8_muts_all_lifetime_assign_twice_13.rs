::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn test() {
    let x: u8;
    x = 5;
    x = 7;

}
}
