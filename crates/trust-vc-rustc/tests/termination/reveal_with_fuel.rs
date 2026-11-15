verus! {
spec fn count_down(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { 1 + count_down((i - 1) as nat) }
}

proof fn properties() {
    reveal_with_fuel(count_down, 2);
    assert(count_down(1) == 1);
}
}
