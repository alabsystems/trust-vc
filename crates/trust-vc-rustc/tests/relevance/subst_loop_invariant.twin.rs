verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn t(b: bool, c: bool, x: u64)
    requires
        (if x == 1 { b } else { x == 1 }),
        s(x as int) == s(1),
{
    let mut i: u64 = 0;
    while i < 3
        invariant
            (if x == 1 { b } else { x == 2 }),
            s(x as int) == s(1),
        decreases 3 - i
    {
        proof { assert(s(0) == 0); }
        proof { assert(s(2) == 3); }
        i = i + 1;
    }
}
}
