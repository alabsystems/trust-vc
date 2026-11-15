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
fn test(b: bool) {
    let mut i: i8 = 0;
    'x: loop
        invariant i == 0
    {
        i = i + 1;
        'y: loop
            invariant i == 1
        {
            break 'x;
        }
        i = i - 1;
        if b {
            break;
        }
    }
    assert(i == 0);
}
}
