::verus_builtin_macros::verus!{
struct S { a: u64 }
fn mset(x: &mut u64) ensures *x == 7 { *x = 7; }
fn t() { let mut s = S { a: 0 }; #[verifier::trigger] s.a = 5; assert(s.a == 5); }
}
