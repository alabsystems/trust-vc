::verus_builtin_macros::verus!{
proof fn test_ret(a: int, b: int) -> (ret: int)
    requires
        a <= b,
    ensures
        #![verifier::proof_note("Test label #3")]
        ret <= a + b,
        ret <= a + a, // FAILS
        ret <= b + b,
{
    a + b
}
}
::verus_builtin_macros::verus!{
proof fn test_ret2(a: int, b: int) -> (ret: int)
    requires
        a <= b,
    ensures
        ret <= a + b,
        ret <= a + a,
        ret <= b + b,
{
    let mut x = test_ret(a, a);
    #[verifier::proof_note("m")] x = test_ret(x, x);
    assert(x <= 4 * a);
    x = test_ret(b, b);
    x = test_ret(x, x);
    assert(x <= 4 * b);
    x = test_ret(a + 1, a + 2);
    x = test_ret(x + 3, x + 4);
    assert(x <= 4 * a + 4 + 6);
    x = test_ret(a, b);
    x
}
}
