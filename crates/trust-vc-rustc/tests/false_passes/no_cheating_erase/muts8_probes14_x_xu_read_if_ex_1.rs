::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn test(b: bool) { let v: u64; if b { let y: u64 = v; } }
}
