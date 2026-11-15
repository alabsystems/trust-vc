::verus_builtin_macros::verus!{
fn t() { let ghost mut g: int = 0; proof { g = 5; } assert(g == 5); }
}
