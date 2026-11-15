verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn w(i: int) -> bool { s(i) == s(1) }
fn t(x: u64)
    requires
        x + 1 == 2,
        k(1) > 0,
{
    let mut j: u64 = 0;
    while j < 1
        invariant
            x + 1 == 2,
            k(1) > 0,
            j <= 1,
        decreases 1 - j,
    {
        proof { assume(w(x as int)); }
        assert(s(0) == 0);
        assert(s(2) == 3);
        j = j + 1;
    }
}
}
