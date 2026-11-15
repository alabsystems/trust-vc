::verus_builtin_macros::verus!{
spec fn at_least_twice_as_big_a(a: int, b: int) -> bool {
    a >= 2 * b
}

// this is less interesting in Verus because, contrary to Dafny, there's no predicate keyword
// in Verus
spec fn at_least_twice_as_big_b(a: int, b: int) -> bool {
    a >= 2 * b
}

spec fn double(a: int) -> int {
    2 * a
}
}
::verus_builtin_macros::verus!{
proof fn these_two_predicates_are_equivalent(x: int, y: int)
{
    assert(at_least_twice_as_big_a(x, y) == at_least_twice_as_big_b(x, y));
}

proof fn four_times_is_pretty_big(x: int)
    requires x >= 0
{ reveal_with_fuel(at_least_twice_as_big_b, 0u32);
    assert(at_least_twice_as_big_a(double(double(x)), x));
}
}
