::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
#[verifier::external_body]
spec fn u() -> bool { true }
struct S { x: u8 }
fn consume(s: S) {}
fn f() {
    let s = S { x: 1 };
    consume(s);

}

}
