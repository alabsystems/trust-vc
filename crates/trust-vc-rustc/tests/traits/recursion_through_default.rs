::verus_builtin_macros::verus!{
trait T {
    proof fn f() ensures false { Self::g() }
    proof fn g() ensures false;
}
proof fn h() ensures false { <bool as T>::f(); }
impl T for bool {
    proof fn g() { assume(false); }
}
}
