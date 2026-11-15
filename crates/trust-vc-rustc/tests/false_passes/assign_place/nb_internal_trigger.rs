::verus_builtin_macros::verus!{
fn t() { let mut x: u64 = 0; #[verus::internal(trigger)] x = 5; assert(x == 5); }
}
