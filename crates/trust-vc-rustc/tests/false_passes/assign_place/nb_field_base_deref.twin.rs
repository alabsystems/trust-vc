::verus_builtin_macros::verus!{
struct S { a: u64 }
fn t(s: &mut S) ensures s.a == 5 { (s).a = 5; }
}
