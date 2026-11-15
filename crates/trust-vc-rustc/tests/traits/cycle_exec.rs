::verus_builtin_macros::verus!{
trait T { fn f(&self) -> u8; }
fn g<A: T>(a: &A) -> u8 { a.f() }
struct S;
impl T for S { fn f(&self) -> u8 { 1 } }
}
