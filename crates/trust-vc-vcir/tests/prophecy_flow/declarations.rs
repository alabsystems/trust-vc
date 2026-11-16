//! Prophecy-flow regression cases. Root wrappers preserve the test roster.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn only_spec_functions_and_ghost_declarations_can_be_marked_prophetic() {
    let mut caller = function(2, Mode::Proof, Ty::Unit);
    caller.attrs.prophetic = true;
    let mut krate = source(vec![caller]);
    rejected(
        &krate,
        2,
        "prophetic attribute can only be applied to 'spec' functions",
    );
    krate.fns[1].attrs.prophetic = false;
    for prophecy in [DeclProphecy::Prophetic, DeclProphecy::DelayedInfer] {
        let target = add(
            &mut krate.fns[1],
            Ty::Bool,
            Mode::Proof,
            LocalKind::Let,
            prophecy,
        );
        krate.fns[1].body = Body::Stmts(Block::new(vec![let_stmt(target, Some(boolean(false)))]));
        rejected(&krate, 2, "only a ghost variable can be prophetic");
    }
}

pub(super) fn checked_imported_definition_cannot_change_the_signature_prophecy_effect() {
    for prophetic in [false, true] {
        let mut declaration = function(2, Mode::Spec, Ty::Bool);
        declaration.attrs.prophetic = prophetic;
        declaration.body = Body::Spec(boolean(true));
        let mut semantic = VcCrate::new("checked definition");
        semantic.fns.push(declaration.clone());
        let definitions = CheckedSpecDefinitions::from_crate(&semantic, &[id(2)]).unwrap();
        declaration.role = FnRole::Imported;
        declaration.body = Body::None;
        let mut client = VcCrate::new("imported signature");
        client.fns.push(declaration);
        let before = client.clone();
        assert!(definitions.validate_for_crate(&client).is_ok());
        assert_eq!(
            vcgen::generate_with_spec_definitions(&client, &definitions).get(id(2)),
            Some(&FnVcs::Declared)
        );
        client.fns[0].attrs.prophetic = !prophetic;
        assert!(definitions.validate_for_crate(&client).is_err());
        assert!(matches!(
            vcgen::generate_with_spec_definitions(&client, &definitions).get(id(2)),
            Some(FnVcs::Refused(_))
        ));
        assert_eq!(before.fns[0].body, Body::None);
    }
}
