::verus_builtin_macros::verus!{
trait T {
    fn g() -> (r: u8) ensures r == 7 { 7 }
    fn h() -> (r: u8) ensures r == 7 { 7 }
}
struct S;
impl T for S {}
fn bad() {
    let x = S::g();
    assert(x == 7);
}
}
