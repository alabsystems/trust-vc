#![feature(fmt_internals)]
#![allow(unused_imports, unused_macros, deprecated, non_snake_case, non_camel_case_types, non_upper_case_globals)]
#![feature(allocator_api)]
#![feature(proc_macro_hygiene)]
#![feature(never_type)]
#![feature(core_intrinsics)]
#![feature(ptr_metadata)]
#![feature(sized_hierarchy)]
#![feature(const_destruct)]
use verus_builtin::*;
use verus_builtin_macros::*;
verus! {
#[derive(Copy, Clone)]
enum E { A = 3, B = 9 }
fn code(e:E) -> (r:u8)
  ensures r == (match e { E::A => 3u8, E::B => 9u8 }),
{
  let copied = e.clone();
  match copied { E::A => copied as u8, E::B => copied as u8 }
}
fn check() {
  let a = code(E::A); let b = code(E::B);
  assert(a == 3u8); assert(b == 9u8);
}
}
