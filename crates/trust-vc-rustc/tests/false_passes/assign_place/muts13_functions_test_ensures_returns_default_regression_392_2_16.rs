::verus_builtin_macros::verus!{
spec fn foo() -> bool { true }

fn returns_unit() ensures foo() { }

fn test(b: bool) {
    let x: ();
    if b {
        #[verifier::proof_note("m")] x = returns_unit();
    }
}
}
