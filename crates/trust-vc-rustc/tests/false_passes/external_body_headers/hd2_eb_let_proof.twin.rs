::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { let x: u8 = 5;  }
proof fn user() { f(); }
}
