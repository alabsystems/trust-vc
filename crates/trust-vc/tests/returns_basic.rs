// tests/returns_basic.rs
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache 2.0

//! Tests for the #[returns] attribute macro

use trust_vc::returns;

#[test]
fn test_returns_basic() {
    // Test that #[returns] allows naming the return value
    #[returns(res)]
    fn add_one(x: i32) -> i32 {
        x + 1
    }

    let result = add_one(5);
    assert_eq!(result, 6);
}

#[test]
fn test_returns_with_tuple() {
    // Test #[returns] with tuple return type
    #[returns(pair)]
    fn make_pair(x: i32, y: i32) -> (i32, i32) {
        (x, y)
    }

    let result = make_pair(3, 4);
    assert_eq!(result, (3, 4));
}

#[test]
fn test_returns_with_option() {
    // Test #[returns] with Option type
    #[returns(opt)]
    fn safe_divide(x: i32, y: i32) -> Option<i32> {
        if y == 0 {
            None
        } else {
            Some(x / y)
        }
    }

    assert_eq!(safe_divide(10, 2), Some(5));
    assert_eq!(safe_divide(10, 0), None);
}

#[test]
fn test_returns_with_result() {
    // Test #[returns] with Result type
    #[returns(res)]
    fn checked_add(x: i32, y: i32) -> Result<i32, &'static str> {
        x.checked_add(y).ok_or("overflow")
    }

    assert!(checked_add(1, 2).is_ok());
    assert!(checked_add(i32::MAX, 1).is_err());
}

#[test]
fn test_returns_in_impl_block() {
    struct Counter {
        value: i32,
    }

    impl Counter {
        #[returns(new_value)]
        fn increment(&mut self) -> i32 {
            self.value += 1;
            self.value
        }
    }

    let mut counter = Counter { value: 0 };
    assert_eq!(counter.increment(), 1);
    assert_eq!(counter.increment(), 2);
}

#[test]
fn test_returns_with_generic_type() {
    // Test #[returns] with generic function
    #[returns(result)]
    fn identity<T>(x: T) -> T {
        x
    }

    assert_eq!(identity(42), 42);
    assert_eq!(identity("hello"), "hello");
}

#[test]
fn test_returns_with_reference() {
    // Test #[returns] with reference return type
    #[returns(ref_result)]
    fn get_first<'a>(items: &'a [i32]) -> Option<&'a i32> {
        items.first()
    }

    let numbers = vec![1, 2, 3];
    assert_eq!(get_first(&numbers), Some(&1));

    let empty: Vec<i32> = vec![];
    assert_eq!(get_first(&empty), None);
}

#[test]
fn test_returns_with_async_function() {
    // Test #[returns] with async function
    #[returns(future_result)]
    async fn async_add(x: i32, y: i32) -> i32 {
        x + y
    }

    // Note: Can't actually await in non-async test context
    // This just verifies the macro doesn't break async functions
    drop(async_add(1, 2));
}

#[test]
fn test_returns_with_impl_trait() {
    // Test #[returns] with impl Trait return type
    #[returns(iter_result)]
    fn get_iterator() -> impl Iterator<Item = i32> {
        vec![1, 2, 3].into_iter()
    }

    let mut iter = get_iterator();
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next(), Some(2));
    assert_eq!(iter.next(), Some(3));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_returns_with_box_dyn() {
    // Test #[returns] with Box<dyn Trait> return type
    trait MyTrait {
        fn value(&self) -> i32;
    }

    struct MyStruct(i32);
    impl MyTrait for MyStruct {
        fn value(&self) -> i32 {
            self.0
        }
    }

    #[returns(boxed_trait)]
    fn get_trait_object(x: i32) -> Box<dyn MyTrait> {
        Box::new(MyStruct(x))
    }

    let obj = get_trait_object(42);
    assert_eq!(obj.value(), 42);
}
