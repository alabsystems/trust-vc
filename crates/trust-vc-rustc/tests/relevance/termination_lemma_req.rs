verus! {
spec fn m(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else { m(n - 1) + 1 }
}
proof fn f(n: int)
    requires (if m(n - 1) > 7 { 1int } else { 2int }) != 3,
    decreases m(n)
{
    if n > 1 { f(n - 2); }
}
}
