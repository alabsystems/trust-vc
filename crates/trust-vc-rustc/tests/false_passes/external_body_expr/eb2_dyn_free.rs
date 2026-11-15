::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: &dyn Fn()| 0u8); }
fn user() {{ f(); }}
}
