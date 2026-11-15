::verus_builtin_macros::verus!{
#[verifier(external_body)]
fn f<A>(a: &A) { let x: u8 = 5; let y: u8 = x; requires(false); }
fn user(x: u8) { f(&x); }
}
