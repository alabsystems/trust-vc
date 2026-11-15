::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn test1() {
    let x: u64;
    #[allow(unused_assignments)]
    x = 23;
    x = 23;
}
}
