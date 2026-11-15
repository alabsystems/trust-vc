verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn t(b: bool, c: bool, x: u64)
    requires
        (if b { x as int } else { 2int }) <= 1,
        s(x as int) == s(1),
{
    proof { assert(s(0) == 0); }
    proof { assert(s(2) == 3); }
}
}
