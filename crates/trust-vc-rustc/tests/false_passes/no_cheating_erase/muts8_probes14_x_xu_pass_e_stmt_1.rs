::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn e_take(a: u64) { }
fn test(b: bool) { let v: u64; e_take(v); }
}
