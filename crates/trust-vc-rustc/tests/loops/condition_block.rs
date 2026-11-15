verus! {
fn test1() {
    let mut i: u32 = 0;
    let mut x: u32 = 0;
    while {x = x + 1; i < 10}
        invariant
            i <= 10,
            x == i,
        decreases 10 - i
    {
        i = i + 1;
    }
    assert(i == 10);
    assert(x == 11);
}
}
