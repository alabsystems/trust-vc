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
verus! {
fn test_old_in_ensures(a: &mut u64)
    requires *old(a) < 2000,
    ensures *a as int === *old(a) + 26,
{
    let mut i: u64 = 0;
    loop
        invariant *old(a) < 2000,
            0 <= i, i < 25,
            *a as int === *old(a) + i,
    {
        *a = *a + 1;
        i = i + 1;
        if i == 25 {
            return;
        }
    }
}
}
