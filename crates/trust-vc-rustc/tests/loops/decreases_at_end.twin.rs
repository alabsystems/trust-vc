verus! {
fn f() {
    let mut i: u32 = 0;
    while i < 10
        invariant i <= 10
        decreases i
    {
        i = i + 1;
    }
}
}
