trait A {
    fn no_good(&self) {}
}

struct S;

impl A for S {
    #[verifier::external_body]
    fn no_good(&self) {}
}
