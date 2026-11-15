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
use verus_builtin::*;
use verus_builtin_macros::*;

::verus_builtin_macros::verus!{
spec fn tr<A>(a: A) -> bool {
    true
}

proof fn test1() {
    assert(tr::<nat>(300));
    assert(exists|i: nat| i >= 0 && tr(i));
}
}
