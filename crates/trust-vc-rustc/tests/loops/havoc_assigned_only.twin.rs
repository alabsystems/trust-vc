verus! {
fn f() {
    let mut i: u32 = 0;
    let mut j: u32 = 5;
    while i < 3
        invariant i <= 3
        decreases 3 - i
    {
        i = i + 1;
        j = j;
    }
    assert(j == 5);
}
}
