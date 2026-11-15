::verus_builtin_macros::verus!{
fn t() { let mut x: u64 = 0; x = 6; assert(x == 5); }
}
