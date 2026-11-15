::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
spec fn foo() -> bool { true }

fn returns_unit() ensures foo() { }

fn test(b: bool) {
    let x: ();
    if b {
        x = returns_unit();

    }
}
}
