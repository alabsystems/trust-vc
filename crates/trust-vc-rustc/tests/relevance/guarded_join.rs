verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t(c: bool, x: int) {
    let mut y: nat = 0;
    if c {
        assume(s(1) == 1 + x);
        y = 1;
    } else {
        y = 2;
    }
    assert(s(0) == 0); assert(s(1) == 1);
    assert(s(2) == 3);
}
}
