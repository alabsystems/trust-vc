::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    fn f(&self) -> (r: u8) ensures r == 7;
}
fn user<A: T>(a: &A) { let r = a.f(); assert(r == 8); }
}
