::verus_builtin_macros::verus!{
#[verifier(external_body)]
proof fn f<A>(a: A) { let x: u8 = 5; let y: u8 = x; requires(false); }
proof fn user() { f(1u8); }
}
