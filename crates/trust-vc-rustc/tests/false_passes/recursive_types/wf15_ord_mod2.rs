::verus_builtin_macros::verus!{
pub mod m { pub struct Q { pub q: &'static Q } }
pub mod n { pub mod k { pub struct K { pub k: &'static K } } }
pub struct P { pub p: &'static P }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
