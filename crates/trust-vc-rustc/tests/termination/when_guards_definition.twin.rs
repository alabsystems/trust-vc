verus! {
spec fn f(i: int) -> int
    decreases i
    when i >= 0
{
    if i == 0 { 0 } else { i + f(i - 1) }
}

proof fn properties() {
    assert(f(-1) == -1 + f(-2));
}
}
