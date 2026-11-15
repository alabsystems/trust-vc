::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) -> (r: bool) ensures r == (a || b) { let mut c = a; c = c || b; c }
}
