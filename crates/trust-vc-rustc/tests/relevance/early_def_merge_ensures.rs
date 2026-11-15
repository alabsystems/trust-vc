verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn sn(n: nat) -> int
    decreases n
{
    if n == 0 { 0 } else { n + sn((n - 1) as nat) }
}
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
spec fn w(i: int) -> bool { s(i) == s(1) }
spec fn rn(i: nat) -> bool
    decreases i
{
    if i == 0 { true } else { s(i as int) == s(1) && rn((i - 1) as nat) }
}
spec fn rn2(i: nat) -> bool
    decreases i
{
    if i == 0 { true } else { sn(i) == sn(1) && rn2((i - 1) as nat) }
}
spec fn rn3(i: int) -> bool
    decreases i
{
    if i <= 0 { true } else { sn(i as nat) == sn(1) && rn3(i - 1) }
}
spec fn ru(i: u64) -> bool
    decreases i
{
    if i == 0 { true } else { s(i as int) == s(1) && ru((i - 1) as u64) }
}
spec fn rp(i: int, j: int) -> bool
    decreases i
{
    if i <= 0 { true } else { s(i) == s(j) && rp(i - 1, j) }
}
spec fn rq(i: int) -> bool
    decreases i
{
    if i <= 0 { true } else { s(i) == s(1) || rq(i - 1) }
}
proof fn lw(i: int)
    ensures w(i)
{
    admit();
}
proof fn t(x: int)
    requires
        v(x),
        k(1) > 0,
{
    lw(x);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
