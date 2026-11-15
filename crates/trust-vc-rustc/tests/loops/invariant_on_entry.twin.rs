verus! {
fn f() {
    let mut i: u32 = 11;
    while i < 10
        invariant i <= 10
        decreases 10 - i
    {
        i = i + 1;
    }
}
}
