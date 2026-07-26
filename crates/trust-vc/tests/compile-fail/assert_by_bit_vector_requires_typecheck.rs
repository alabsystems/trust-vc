#![allow(unexpected_cfgs)]

use trust_vc::assert_by_bit_vector;

fn main() {
    let x: u32 = 0;
    assert_by_bit_vector! {
        true;
        requires no_such_fn(x)
    };
}
