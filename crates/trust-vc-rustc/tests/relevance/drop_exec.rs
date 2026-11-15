verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn t() {
    assert(s(0) >= s(0) && s(1) >= s(1));
    assert(s(2) == 3);
}
}
