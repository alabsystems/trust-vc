verus! {
spec fn m(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else { m(n - 1) + 1 }
}
spec fn f(n: int) -> int
    decreases m(n)
{
    if n <= 1 || (if m(n - 1) > 7 { 1int } else { 2int }) == 1 { 0 } else { f(n - 2) }
}
}
