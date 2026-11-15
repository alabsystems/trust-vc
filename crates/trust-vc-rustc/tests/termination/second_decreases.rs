verus! {
spec fn f(i: nat) -> nat
{
    decreases(i);
    decreases(i);
    if i == 0 { 0 } else { 1 + f((i - 1) as nat) }
}
}
