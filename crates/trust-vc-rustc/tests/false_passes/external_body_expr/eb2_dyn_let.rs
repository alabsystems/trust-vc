::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; (|x: &dyn Fn()| 0u8); }
fn user() {{ f(); }}
}
