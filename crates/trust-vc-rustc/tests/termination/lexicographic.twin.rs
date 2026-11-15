verus! {
proof fn dec2(j: nat, k: nat)
    decreases j, k
{
    if 0 < k {
        dec2(j, k);
    }
    if 0 < j {
        dec2((j - 1) as nat, 100 * j + k);
    }
}
}
