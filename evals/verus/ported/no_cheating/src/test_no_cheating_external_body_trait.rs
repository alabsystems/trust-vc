trait A {
    #[verifier::external_body]
    fn no_good(&self) {}
}
