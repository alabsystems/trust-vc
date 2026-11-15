//! Registry mutation helpers for the verification bridge.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[doc(hidden)]
pub fn register_proof(name: &str, obligations: Vec<ProofObligation>) {
    REGISTERED_PROOFS.with(|proofs| {
        proofs.borrow_mut().push(ProofRegistration {
            name: name.to_string(),
            obligations,
        });
    });
}

pub(crate) fn register_collection_error(err: TrustVcError) {
    COLLECTION_ERROR.with(|slot| {
        if let Ok(mut slot) = slot.try_borrow_mut() {
            if slot.is_none() {
                *slot = Some(err);
            }
        }
    });
}

#[doc(hidden)]
pub fn clear_registrations() {
    // Graceful skip on borrow conflict: panicking during cleanup aborts later clears.
    REGISTERED_PROOFS.with(|proofs| {
        if let Ok(mut guard) = proofs.try_borrow_mut() {
            guard.clear();
        }
    });
    #[cfg(feature = "ty")]
    PROTOCOL_OBLIGATIONS.with(|proto| {
        if let Ok(mut guard) = proto.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_STATE_VARS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_ACTIONS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_INVARIANTS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_LIVENESS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    COLLECTION_ERROR.with(|slot| {
        if let Ok(mut guard) = slot.try_borrow_mut() {
            let _ = guard.take();
        }
    });
    crate::trait_registry::clear_registered_traits();
}

#[cfg(feature = "ty")]
#[doc(hidden)]
pub fn register_protocol(obligation: ProtocolObligation) {
    PROTOCOL_OBLIGATIONS.with(|proto| {
        proto.borrow_mut().push(obligation);
    });
}

/// Register a protocol state variable by name and type. It starts at its
/// type's zero (`0` or `false`); a `#[protocol]` struct's fields start at the
/// struct's `Default::default()` ([`register_protocol_field`]).
#[doc(hidden)]
pub fn register_protocol_state_var(protocol_name: &str, field_name: &str, rust_type: &str) {
    push_protocol_state_var(protocol_name, field_name, rust_type, ProtocolInitial::Zero);
}

fn push_protocol_state_var(
    protocol_name: &str,
    field_name: &str,
    rust_type: &str,
    initial: ProtocolInitial,
) {
    PROTOCOL_STATE_VARS.with(|vars| {
        vars.borrow_mut().push(ProtocolStateVarDef {
            protocol_name: protocol_name.to_string(),
            field_name: field_name.to_string(),
            rust_type: rust_type.to_string(),
            initial,
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_action(protocol_name: &str, name: &str, body: &str) {
    PROTOCOL_ACTIONS.with(|actions| {
        actions.borrow_mut().push(ProtocolActionDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            body: body.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_invariant(protocol_name: &str, name: &str, expr: &str) {
    PROTOCOL_INVARIANTS.with(|invs| {
        invs.borrow_mut().push(ProtocolInvariantDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            expr: expr.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_liveness(protocol_name: &str, name: &str, expr: &str, fairness: &str) {
    PROTOCOL_LIVENESS.with(|props| {
        props.borrow_mut().push(ProtocolLivenessDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            expr: expr.to_string(),
            fairness: fairness.to_string(),
        });
    });
}

/// A `#[action]`, `#[safety]` or `#[liveness]` component, recorded where it is
/// declared: a protocol's model holds every component its source declares,
/// whether or not the component's function ever runs.
#[doc(hidden)]
pub struct ProtocolComponentDef {
    /// The protocol the component's attribute names, as a type.
    pub protocol: fn() -> std::any::TypeId,
    pub kind: ProtocolComponentKind,
    pub name: &'static str,
    pub body: &'static str,
    pub fairness: &'static str,
}

#[doc(hidden)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProtocolComponentKind {
    Action,
    Safety,
    Liveness,
}

inventory::collect!(ProtocolComponentDef);

/// Register, under `protocol_name`, every component declared for the protocol
/// type `protocol` (see [`ProtocolComponentDef`]).
#[doc(hidden)]
pub fn register_declared_protocol_components(protocol_name: &str, protocol: std::any::TypeId) {
    let mut declared: Vec<&ProtocolComponentDef> = inventory::iter::<ProtocolComponentDef>
        .into_iter()
        .filter(|def| (def.protocol)() == protocol)
        .collect();
    // Link order is not source order: register in one order in every build.
    declared.sort_by_key(|def| (def.kind, def.name));
    for def in declared {
        match def.kind {
            ProtocolComponentKind::Action => {
                register_protocol_action(protocol_name, def.name, def.body)
            }
            ProtocolComponentKind::Safety => {
                register_protocol_invariant(protocol_name, def.name, def.body)
            }
            ProtocolComponentKind::Liveness => {
                register_protocol_liveness(protocol_name, def.name, def.body, def.fairness)
            }
        }
    }
}

/// Register a `#[protocol]` field. `modelled` is the lane's name for the type
/// Rust resolved for the field ([`ProtocolModelledField`]), `None` for a type
/// the lane does not model; `spelled` only names that type in the refusal.
/// `initial` is the field's value in each of two `Default::default()` calls
/// ([`ProtocolInitialState`]), `None` when the struct has no `Default`.
#[doc(hidden)]
pub fn register_protocol_field(
    protocol_name: &str,
    field_name: &str,
    modelled: Option<&'static str>,
    spelled: &str,
    initial: Option<[Option<ProtocolValue>; 2]>,
) {
    let rust_type = match modelled {
        Some(name) => name.to_string(),
        None => format!("`{spelled}`"),
    };
    let initial = match initial {
        Some(values) => ProtocolInitial::Default(values),
        None => ProtocolInitial::NoDefault,
    };
    push_protocol_state_var(protocol_name, field_name, &rust_type, initial);
}

/// The value of a `#[protocol]` field of a type the lane models.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProtocolValue {
    Bool(bool),
    Int(i128),
}

/// A `#[protocol]` struct's initial state, as Rust builds it:
/// `Default::default()`. Method resolution on `&ProtocolInitialState<T>`
/// selects [`ProtocolDefaultState`] when `T: Default` and
/// [`ProtocolNoDefaultState`] otherwise.
#[doc(hidden)]
pub struct ProtocolInitialState<T>(pub std::marker::PhantomData<T>);

#[doc(hidden)]
pub trait ProtocolDefaultState {
    type State;
    /// `Default::default()`, called twice: a `Default` that returns two
    /// different states has no one initial state.
    fn protocol_initial_states(&self) -> Option<[Self::State; 2]>;
}

#[doc(hidden)]
pub trait ProtocolNoDefaultState {
    type State;
    fn protocol_initial_states(&self) -> Option<[Self::State; 2]>;
}

impl<T: Default> ProtocolDefaultState for ProtocolInitialState<T> {
    type State = T;
    fn protocol_initial_states(&self) -> Option<[T; 2]> {
        Some([T::default(), T::default()])
    }
}

impl<T> ProtocolNoDefaultState for &ProtocolInitialState<T> {
    type State = T;
    fn protocol_initial_states(&self) -> Option<[T; 2]> {
        None
    }
}

/// The type of a `#[protocol]` field, as Rust resolves it: through an alias,
/// and never by how it is spelled (`type u64 = u8;` makes a field spelled
/// `u64` a `u8`). Method resolution on `&ProtocolFieldType<T>` selects
/// [`ProtocolModelledField`] when `T` is a type the lane models and
/// [`ProtocolUnmodelledField`] otherwise.
#[doc(hidden)]
pub struct ProtocolFieldType<T: ?Sized>(pub std::marker::PhantomData<T>);

#[doc(hidden)]
pub trait ProtocolModelledField {
    type Field;
    fn protocol_type(&self) -> Option<&'static str>;
    fn protocol_value(&self, value: &Self::Field) -> Option<ProtocolValue>;
}

#[doc(hidden)]
pub trait ProtocolUnmodelledField {
    type Field: ?Sized;
    fn protocol_type(&self) -> Option<&'static str>;
    fn protocol_value(&self, value: &Self::Field) -> Option<ProtocolValue>;
}

impl<T: ?Sized> ProtocolUnmodelledField for &ProtocolFieldType<T> {
    type Field = T;
    fn protocol_type(&self) -> Option<&'static str> {
        None
    }
    fn protocol_value(&self, _: &T) -> Option<ProtocolValue> {
        None
    }
}

impl ProtocolModelledField for ProtocolFieldType<bool> {
    type Field = bool;
    fn protocol_type(&self) -> Option<&'static str> {
        Some("bool")
    }
    fn protocol_value(&self, value: &bool) -> Option<ProtocolValue> {
        Some(ProtocolValue::Bool(*value))
    }
}

macro_rules! modelled_field_types {
    ($($ty:ident)*) => {
        /// The field types the lane models, by the name its translator reads.
        #[cfg(all(test, feature = "ty"))]
        pub(crate) const MODELLED_FIELD_TYPES: &[&str] = &["bool", $(stringify!($ty)),*];
        $(
            impl ProtocolModelledField for ProtocolFieldType<::core::primitive::$ty> {
                type Field = ::core::primitive::$ty;
                fn protocol_type(&self) -> Option<&'static str> {
                    Some(stringify!($ty))
                }
                fn protocol_value(&self, value: &Self::Field) -> Option<ProtocolValue> {
                    i128::try_from(*value).ok().map(ProtocolValue::Int)
                }
            }
        )*
    };
}

modelled_field_types!(u8 u16 u32 u64 usize i8 i16 i32 i64);
