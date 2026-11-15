::verus_builtin_macros::verus!{
fn need<F: Fn()>(f: F) {}
fn f() { assert(1 + 1 == 2); }
}
