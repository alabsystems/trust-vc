::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f<A>(a: A) { fn inner() {} requires(false); }
proof fn user() { f(1u8); }
}
