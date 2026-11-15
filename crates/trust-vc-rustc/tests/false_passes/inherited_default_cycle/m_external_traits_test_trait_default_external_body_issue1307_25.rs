::verus_builtin_macros::verus!{

        #[verifier::external]
        fn some_external_fn() { }

        trait T {
            #[verifier(external_body)]
            fn f1() -> (ret: bool)
                ensures
                    !ret
            {
                some_external_fn();
                false
            }

            fn f2() -> bool {
                S::f1()
            }
        }

        struct S;

        impl T for S { }
    }
