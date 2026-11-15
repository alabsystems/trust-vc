#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Write the method names the syn lane's library models declare.

Every `fn` whose first parameter is a `self` receiver (`self`, `mut self`,
`&self`, `&'a mut self`, `self: Box<Self>`) in the given source roots is a
method some library type or trait has. The trait-method-resolution rule of
the syn lane (`crates/trust-vc-core/src/vc_extraction/trait_method_resolution.rs`)
treats a method name outside this list as one no std, vstd or trust-vc-types
type has, so the list must be a superset: pass every root the lane models.

Usage (the roots the committed list was built from; $TRUST is a checkout of
the Trust superproject and $VERUS one of Verus):

    scripts/gen_library_method_names.py \
        "$TRUST"/library/core/src "$TRUST"/library/alloc/src \
        "$TRUST"/library/std/src "$TRUST"/library/portable-simd/crates/core_simd/src \
        "$VERUS"/source/vstd crates/trust-vc-types/src crates/trust-vc-std \
        > crates/trust-vc-core/src/vc_extraction/library_method_names.txt

A method whose name a macro builds from a parameter (`fn $method(self, ..)`)
is not read here; in the std sources above each such macro implements a trait
whose own declaration spells the name, so the name is listed through it.
"""

import os
import re
import sys

RECEIVER_METHOD = re.compile(
    r"\bfn\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^;{]*?>)?\s*\(\s*"
    r"(?:#\[[^\]]*\]\s*)*(?:&\s*(?:'[A-Za-z_]+\s+)?)?(?:mut\s+)?self\b",
    re.S,
)
LINE_COMMENT = re.compile(r"//[^\n]*")


def names_in(root):
    names = set()
    for directory, _, files in os.walk(root):
        for name in files:
            if not name.endswith(".rs"):
                continue
            with open(os.path.join(directory, name), encoding="utf-8", errors="replace") as f:
                source = LINE_COMMENT.sub("", f.read())
            names.update(RECEIVER_METHOD.findall(source))
    return names


def main(roots):
    if not roots:
        sys.exit(__doc__)
    names = set()
    for root in roots:
        if not os.path.isdir(root):
            sys.exit(f"not a directory: {root}")
        names |= names_in(root)
    for name in sorted(names):
        print(name)


if __name__ == "__main__":
    main(sys.argv[1:])
