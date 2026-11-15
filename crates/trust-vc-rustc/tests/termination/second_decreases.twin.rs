verus! {
spec fn f(i: nat) -> nat
{
    decreases(i);
    recommends(true);
    if i == 0 { 0 } else { 1 + f((i - 1) as nat) }
}
}
