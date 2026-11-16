#![feature(fmt_internals)]

#![allow(unused_imports)]
#![allow(unused_macros)]
#![allow(deprecated)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(unused_comparisons)]
#![allow(noop_method_call)]
#![feature(allocator_api)]
#![feature(proc_macro_hygiene)]
#![feature(never_type)]
#![feature(core_intrinsics)]
#![feature(ptr_metadata)]
#![feature(sized_hierarchy)]
#![feature(const_destruct)]
#![verifier::exec_allows_no_decreases_clause]
use verus_builtin::*;
use verus_builtin_macros::*;

::verus_builtin_macros::verus!{
spec fn fibo(val: nat) -> nat
    // TODO I think Dafny is pretty successful at inferring decreases.
    decreases val
{
    if val == 0 { 0 }
    else if val == 1 { 1 }
    else { fibo((val - 2) as nat) + fibo((val - 1) as nat) }
}

spec fn max_u64_fibo_arg() -> nat {
    20
}

proof fn fibo_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        reveal_with_fuel(fibo, 2);
        fibo_monotonic(i, (j - 1) as nat);
    } else {
        fibo_monotonic(i, (j - 1) as nat);
        fibo_monotonic(i, (j - 2) as nat);
    }
}

fn max_u64_fibo_arg_bound()
    ensures
        forall|i: nat| i < max_u64_fibo_arg() ==> fibo(i) < 7000,
{
    assert(fibo(20) == 6765) by {
        reveal_with_fuel(fibo, 11);
    }

    // TODO(chris): "Could not automatically infer triggers for this quantifier." but there's fibo
    // RIGHT THERE! Error should say "matching loop" instead.
    // assume(forall(|i:nat| fibo(i) < fibo(i+1)));

    assert forall|i: nat, j: nat| i <= j implies fibo(i) <= fibo(j) by {
        fibo_monotonic(i, j);
    }
}

fn fibo_recursive_impl(val: u64) -> (f: u64)
    requires
        val < max_u64_fibo_arg(),
    ensures
        fibo(val as nat) == f,
    decreases val
{
    assume(val > 1);

    max_u64_fibo_arg_bound();

    if val == 0 { 0 }
    else if val == 1 { 1 }
    else { fibo_recursive_impl(val - 2) + fibo_recursive_impl(val - 1) }
}

proof fn check()
    ensures
        fibo(0) == 0,
        fibo(20) == 6765,
{
    // Dafny gives lots of fuel for application on literals, which makes examples
    // like this go through like magic. Verus needs you to goose the throttle manually.
    reveal_with_fuel(fibo, 11); // Apparently we get 2 recursions for each drop of fuel.
}

fn main() {
    let mut x: u64 = 0;
    while x < 20 {
        let f = fibo_recursive_impl(x);
        x = x + 1;
    }
}
}
