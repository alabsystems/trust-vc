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

macro_rules! mk { () => { impl Drop for S { fn drop(&mut self) {} } } }
::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e() { mk!(); }
fn user(s: S) -> T { s.t }
fn g() { assert(1 + 1 == 3); }
}

