::verus_builtin_macros::verus!{
struct S { x: u8 }
fn need<F: Fn() + 'static>(f: F) {}
#[verifier::external_body]
fn e() { let v: u8 = 1; need(move || { let w = v; }); }
fn f() { assert(1 + 1 == 2); }
}
