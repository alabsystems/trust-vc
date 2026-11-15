verus! {
proof fn chained(x: int)
    requires 0 <= x < 10
{
    assert(0 < x <= 9);
}
}
