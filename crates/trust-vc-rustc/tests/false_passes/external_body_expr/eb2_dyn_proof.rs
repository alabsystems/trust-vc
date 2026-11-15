::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { (|x: &dyn Fn()| 0u8); }
proof fn user() {{ f(); }}
}
