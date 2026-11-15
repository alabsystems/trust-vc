::verus_builtin_macros::verus!{
pub trait T {
    #[verifier(external_body)]
    fn f(&self) { let x: u8 = 5; let y: u8 = x; requires(false); }
}
fn user<A: T>(s: &A) { s.f(); }
}
