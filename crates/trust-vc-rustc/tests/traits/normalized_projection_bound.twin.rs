verus! {
    struct S<A>(A);
    trait T1 { proof fn f1(); }
    trait T2 { type X; }
    trait T3 { proof fn f3(); }

    impl T1 for bool {
        proof fn f1() { <S<int> as T3>::f3(); }
    }
    impl T2 for int {
        type X = bool;
    }
    impl<A: T2> T3 for S<A> where <A as T2>::X: T1 {
        proof fn f3() {
            <<A as T2>::X as T1>::f1();
        }
    }
    proof fn test() {
        <S<int> as T3>::f3();
    }
}
