verus! {
#[verifier::loop_isolation(false)]
fn t(a: bool, b: bool) {
    loop
        decreases 1int,
    {
        if a {
            if b {
                break;
            }
        }
        assume(false);
    }
    assert(a && b);
}
}
