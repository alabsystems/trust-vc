// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::ensures(true)]
fn test1() {
    {
        let mut x = 5;
        x = 50;
        let _ = x;
    }
    let mut x = 6;
    x = 60;
    let x = 7;
    let _ = x;
    trust_vc::assert!(x == 7);
}

#[trust_vc::ensures(true)]
fn test1_fails() {
    {
        let mut x = 5;
        x = 50;
        let _ = x;
    }
    let mut x = 6;
    x = 60;
    let x = 7;
    let _ = x;
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn test2() {
    let mut x = 6;
    x = 60;
    let x = 7;
    {
        let mut x = 5;
        x = 50;
        let _ = x;
    }
    trust_vc::assert!(x == 7);
}

#[trust_vc::ensures(true)]
fn test2_fails() {
    let mut x = 6;
    x = 60;
    let x = 7;
    {
        let mut x = 5;
        x = 50;
        let _ = x;
    }
    trust_vc::assert!(x == 7);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn test3() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let y = {
        let mut x = 5;
        x = 50;
        x
    };
    trust_vc::assert!(x == 7);
    trust_vc::assert!(y == 50);
}

#[trust_vc::ensures(true)]
fn test3_fails() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let y = {
        let mut x = 5;
        x = 50;
        x
    };
    trust_vc::assert!(x == 7);
    trust_vc::assert!(y == 50);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn test4() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let y = {
        let mut x = 5;
        x = {
            let x = x + 50;
            x + 50
        };
        x
    };
    trust_vc::assert!(x == 7);
    trust_vc::assert!(y == 105);
}

#[trust_vc::ensures(true)]
fn test4_fails() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let y = {
        let mut x = 5;
        x = {
            let x = x + 50;
            x + 50
        };
        x
    };
    trust_vc::assert!(x == 7);
    trust_vc::assert!(y == 105);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn test5() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let x = {
        let mut x = 5;
        x = {
            let x = x + 50;
            x + 50
        };
        x
    };
    trust_vc::assert!(x == 105);
}

#[trust_vc::ensures(true)]
fn test5_fails() {
    let mut x = 6;
    x = 60;
    let x = 7;
    let x = {
        let mut x = 5;
        x = {
            let x = x + 50;
            x + 50
        };
        x
    };
    trust_vc::assert!(x == 105);
    trust_vc::assert!(false);
}
