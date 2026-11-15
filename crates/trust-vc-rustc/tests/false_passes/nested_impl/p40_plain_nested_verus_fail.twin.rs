::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
fn user(s: S) -> T { s.t }
fn g() { assert(1 + 1 == 3); }
}
fn plain() {
    ::verus_builtin_macros::verus!{
        #[verifier::external_body]
        proof fn e() { fn nested() {} }
    }
}
