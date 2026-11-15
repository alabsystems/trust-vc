verus! {
fn f() {
    let mut i: u32 = 0;
    #[verifier::loop_isolation(false)]
    loop
        invariant i <= 10
        decreases 10 - i
    {
        if i >= 9 {
            break;
        }
        i = i + 1;
    }
    assert(i == 10);
}
}
