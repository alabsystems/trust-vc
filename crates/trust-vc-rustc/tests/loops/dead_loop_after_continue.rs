verus! {
fn t() {
    let mut i: u64 = 0;
    while i < 10
        invariant i <= 10,
        decreases 10 - i,
    {
        i += 1;
        continue;
        while i < 10
            invariant i <= 10,
            decreases 10 - i,
        {
            assert(false);
            i += 1;
        }
    }
}
}
