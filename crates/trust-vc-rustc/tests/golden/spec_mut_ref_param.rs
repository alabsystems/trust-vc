// A spec function with a `&mut` parameter is Verus's error, found before
// its body (which assigns, another error) is looked at.
verus! {

spec fn add1(a: &mut u64) {
    *a = add(*a, 1);
}

} // verus!
