::verus_builtin_macros::verus!{
spec fn some_int(x: int) -> int {
    x
}

proof fn proof_fn() {
    some_int(12);
    assert(false); // FAILS
}

proof fn require_false_return_int() -> int
    requires false,
{ reveal_with_fuel(some_int, 0u32);
    13
}

proof fn proof_fn2() {
    7 +
        require_false_return_int(); // FAILS
}


fn exec_fn() {
    5;
    assert(false); // FAILS
}
}
