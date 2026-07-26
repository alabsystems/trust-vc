// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;

use crate::{Map, Multiset, Seq, Set};

/// Trait for converting runtime types to their specification models.
///
/// The `View` trait provides a standard way to convert runtime types
/// (like `Vec<T>`, `HashMap<K, V>`) to their specification equivalents
/// (`Seq<T>`, `Map<K, V>`). This enables cleaner postconditions that
/// reason about spec-level abstractions.
///
/// # Example
///
/// ```text
/// use trust_vc_types::{View, Seq};
///
/// #[trust_vc::ensures(result.view().len() == self.view().len() + 1)]
/// fn push(&mut self, val: T) {
///     // ...
/// }
///
/// #[trust_vc::ensures(s.view().len() == s.view().len())]
/// fn string_reflexive(s: &String) {}
/// ```
///
/// # ay Encoding
///
/// View lowering is type-specific. Built-in collection and string views are
/// modeled as their spec views, while wrapper views such as the supported Cow
/// subset are lowered to the viewed payload. Unsupported view shapes fail
/// closed rather than being assumed as identity conversions.
pub trait View {
    /// The specification type that this runtime type maps to.
    type ViewTy;

    /// Converts the runtime value to its specification model.
    ///
    /// At runtime, this returns a ghost value. During verification, the value
    /// is related to its view by TrustVc's type-specific lowering support.
    #[must_use]
    fn view(&self) -> Self::ViewTy;
}

// Built-in View implementations for std types

impl<T> View for Vec<T> {
    type ViewTy = Seq<T>;

    fn view(&self) -> Seq<T> {
        Seq::empty() // Ghost - ay treats Vec and Seq as equivalent
    }
}

impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    fn view(&self) -> Seq<T> {
        Seq::empty() // Ghost - ay treats arrays and Seq as equivalent
    }
}

impl<T> View for [T] {
    type ViewTy = Seq<T>;

    fn view(&self) -> Seq<T> {
        Seq::empty() // Ghost - ay treats slices and Seq as equivalent
    }
}

impl<T: View> View for Option<T> {
    type ViewTy = Option<T::ViewTy>;

    fn view(&self) -> Option<T::ViewTy> {
        self.as_ref().map(View::view)
    }
}

impl<'a, B> View for Cow<'a, B>
where
    B: ToOwned + View + ?Sized,
{
    type ViewTy = B::ViewTy;

    fn view(&self) -> B::ViewTy {
        self.as_ref().view()
    }
}

impl View for String {
    type ViewTy = Seq<char>;

    fn view(&self) -> Seq<char> {
        Seq::empty() // Ghost - verifier models String via explicit Seq<char> view
    }
}

impl View for str {
    type ViewTy = Seq<char>;

    fn view(&self) -> Seq<char> {
        Seq::empty() // Ghost - verifier models str via explicit Seq<char> view
    }
}

impl<T> View for std::collections::HashSet<T> {
    type ViewTy = Set<T>;

    fn view(&self) -> Set<T> {
        Set::empty() // Ghost - ay treats HashSet and Set as equivalent
    }
}

impl<T> View for std::collections::BTreeSet<T> {
    type ViewTy = Set<T>;

    fn view(&self) -> Set<T> {
        Set::empty() // Ghost - ay treats BTreeSet and Set as equivalent
    }
}

impl<K, V> View for std::collections::HashMap<K, V> {
    type ViewTy = Map<K, V>;

    fn view(&self) -> Map<K, V> {
        Map::empty() // Ghost - ay treats HashMap and Map as equivalent
    }
}

impl<K, V> View for std::collections::BTreeMap<K, V> {
    type ViewTy = Map<K, V>;

    fn view(&self) -> Map<K, V> {
        Map::empty() // Ghost - ay treats BTreeMap and Map as equivalent
    }
}

// Identity views for spec types (they are their own views)

impl<T> View for Seq<T> {
    type ViewTy = Seq<T>;

    fn view(&self) -> Seq<T> {
        Seq::empty() // Ghost - identity at ay level
    }
}

impl<T> View for Set<T> {
    type ViewTy = Set<T>;

    fn view(&self) -> Set<T> {
        Set::empty() // Ghost - identity at ay level
    }
}

impl<K, V> View for Map<K, V> {
    type ViewTy = Map<K, V>;

    fn view(&self) -> Map<K, V> {
        Map::empty() // Ghost - identity at ay level
    }
}

impl<T> View for Multiset<T> {
    type ViewTy = Multiset<T>;

    fn view(&self) -> Multiset<T> {
        Multiset::empty() // Ghost - identity at ay level
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_view_trait_for_vec() {
        let vec = vec![1, 2, 3];
        let _seq_view = vec.view();
    }

    #[test]
    fn test_view_trait_for_seq() {
        let seq = Seq::<i32>::empty();
        let _view = seq.view();
    }

    #[test]
    fn test_view_trait_for_multiset() {
        let multiset = Multiset::<i32>::empty();
        let _view = multiset.view();
    }

    #[test]
    fn test_view_trait_for_option() {
        let value = Some(Seq::<u8>::empty());
        let _view: Option<Seq<u8>> = value.view();
    }

    #[test]
    fn test_view_trait_for_cow() {
        let value: Cow<'_, str> = Cow::Borrowed("abc");
        let _view: Seq<char> = value.view();

        let owned: Cow<'_, str> = Cow::Owned(String::from("def"));
        let _owned_view: Seq<char> = owned.view();
    }
}
