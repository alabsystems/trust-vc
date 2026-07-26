// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

trust_vc::extern_spec! {
    impl u32 {
        #[requires(false)]
        fn count_ones(self) -> u32;
    }
}
