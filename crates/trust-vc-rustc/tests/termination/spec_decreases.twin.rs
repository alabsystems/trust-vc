verus! {
spec fn sum(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + sum(i) }
}
}
