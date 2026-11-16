//! The exact fresh A40 e18 source, with a false implementation twin.
mod common;

const ORIGINAL: &str = include_str!("e18_spec_completion/fibonacci.rs");

fn verdict(run: &common::Run, function: &str) -> String {
    run.record["functions"]
        .as_array()
        .expect("function records")
        .iter()
        .find(|record| record["def_path"] == function)
        .expect("original function")["verdict"]
        .as_str()
        .expect("function verdict")
        .to_string()
}

#[test]
fn recursive_fibonacci_contract_keeps_the_required_spec_definition() {
    let original = common::run_raw("e18_original_recursive_definition", ORIGINAL, &[]);
    assert_eq!(
        verdict(&original, "fibo_recursive_impl"),
        "verified",
        "{original:?}"
    );
}

#[test]
fn a_wrong_recursive_result_is_still_rejected() {
    // This changes the implementation, retaining the original recursive
    // contract; a bad assumed callee contract cannot hide the wrong result.
    let wrong = ORIGINAL.replace(
        "fibo_recursive_impl(val - 2) + fibo_recursive_impl(val - 1)",
        "fibo_recursive_impl(val - 2) + fibo_recursive_impl(val - 1) + 1",
    );
    assert_ne!(wrong, ORIGINAL);
    let wrong = common::run_raw("e18_wrong_recursive_result", &wrong, &[]);
    assert_eq!(
        verdict(&wrong, "fibo_recursive_impl"),
        "failed",
        "{wrong:?}"
    );
    assert_eq!(wrong.outcome(), "verification-failed", "{wrong:?}");
}
