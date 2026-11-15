::verus_builtin_macros::verus!{
struct S { a: u64 }
fn mset(x: &mut u64) ensures *x == 7 { *x = 7; }
fn t() { let mut x: u64 = 0; #[verifier::trigger] x = 5; assert(x == 5); }
}
