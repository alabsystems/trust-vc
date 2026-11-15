::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
fn e_unit() { }
fn test(b: bool) { let v: u64; if b { if v == 0 { e_unit(); } } }
}
