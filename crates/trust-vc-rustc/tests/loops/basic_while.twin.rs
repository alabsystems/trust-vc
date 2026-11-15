verus! {
fn test1() {
    let mut i: u32 = 0;
    while i < 10
        invariant i <= 9
        decreases 10 - i
    {
        i = i + 1;
    }
    assert(i == 10);
}
}
