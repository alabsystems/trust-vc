::verus_builtin_macros::verus!{
spec fn add1_int(i: int) -> int {
    i + 1
}

spec fn add1_int_left(i: int) -> int {
    1 + i
}

spec fn add1_nat(i: nat) -> nat {
    i + 1
}

spec fn add1_nat_left(i: nat) -> nat {
    1 + i
}

spec fn add_nat_nat(i: nat, j: nat) -> nat {
    i + j
}

spec fn add_nat_u8(i: nat, j: u8) -> int {
    i + j
}

spec fn add_u8_nat(i: u8, j: nat) -> int {
    i + j
}

#[verifier(opaque)]
spec fn add1_nat_opaque(i: nat) -> nat {
    i + 1
}

proof fn test0() -> (n: nat)
    ensures true
{
    100
}

proof fn test0x() -> nat { reveal(add_nat_nat);
    100
}

proof fn test1(i: int, n: nat, u: u8) {
    assert(n >= 0);
    assert(u >= 0);
    assert(n + n >= 0);
    assert((add(u, u) as int) < 256);
    assert(u < 100 ==> (add(u, u) as int) < 250);
    assert(add1_int(u as int) == u as int + 1);
    assert(add1_nat(u as nat) == u as nat + 1);
    let n0 = test0();
    assert(n0 >= 0);
    let n0x = test0x();
    assert(n0x >= 0);
    assert(add1_nat_opaque(5) >= 0);
    assert(n / 2 <= n);
    assert(u / 2 <= u);
    assert(u % 10 < 10);
}
}
