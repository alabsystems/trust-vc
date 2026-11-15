verus! {
spec fn count_down_a(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
}

spec fn count_down_b(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
}

proof fn properties() {
    assert(count_down_a(2) == 2);
}
}
