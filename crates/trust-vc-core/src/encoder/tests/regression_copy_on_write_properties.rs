// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn shared_page_refcount() {
    let mut ctx = VerificationContext::new();
    for v in &["refcount", "new_refcount"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nrc_def",
        "new_refcount == refcount + 1",
    )); // fork
    ctx.push_obligation(ProofObligation::assert("is_2", "new_refcount == 2"));
    ctx.push_obligation(ProofObligation::assert("shared", "new_refcount > 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW: fork increases refcount 1 → 2");
}

#[test]
fn write_triggers_copy() {
    let mut ctx = VerificationContext::new();
    for v in &["refcount", "pages_before", "pages_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_copy", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 2")); // shared
    ctx.push_obligation(ProofObligation::assume("pb", "pages_before == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_copy == if refcount > 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "pages_after == pages_before + 1",
    )); // new private page
    ctx.push_obligation(ProofObligation::assert("yes", "needs_copy == 1"));
    ctx.push_obligation(ProofObligation::assert("is_101", "pages_after == 101"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW: refcount=2 → copy needed, 100→101 pages");
}

#[test]
fn no_copy_when_exclusive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refcount", u32_ty());
    ctx.declare_var_typed("needs_copy", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 1")); // exclusive
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_copy == if refcount > 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "needs_copy == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW: refcount=1 → no copy needed");
}

#[test]
fn refcount_decreases_on_unmap() {
    let mut ctx = VerificationContext::new();
    for v in &["old_refcount", "new_refcount"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orc", "old_refcount == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nrc_def",
        "new_refcount == old_refcount - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "new_refcount == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "new_refcount < old_refcount",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW unmap: refcount 3 → 2");
}

#[test]
fn page_freed_when_refcount_zero() {
    let mut ctx = VerificationContext::new();
    for v in &["old_refcount", "new_refcount"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("orc", "old_refcount == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nrc_def",
        "new_refcount == old_refcount - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_free == if new_refcount == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "new_refcount == 0"));
    ctx.push_obligation(ProofObligation::assert("free", "should_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW: refcount 1→0 → free page");
}

#[test]
fn memory_savings_from_sharing() {
    let mut ctx = VerificationContext::new();
    for v in &["total_pages", "unique_pages", "shared_pages", "savings"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tp", "total_pages == 1000")); // virtual pages across processes
    ctx.push_obligation(ProofObligation::assume("up", "unique_pages == 400")); // physical pages used
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "shared_pages == total_pages - unique_pages",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sav_def",
        "savings == shared_pages * 100 / total_pages",
    ));
    ctx.push_obligation(ProofObligation::assert("sp_600", "shared_pages == 600"));
    ctx.push_obligation(ProofObligation::assert("sav_60", "savings == 60")); // 60% savings
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CoW savings: 600/1000 = 60%");
}

#[test]
fn fork_shares_all_pages() {
    let mut ctx = VerificationContext::new();
    for v in &["parent_pages", "child_pages", "physical_pages_used"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pp", "parent_pages == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "child_pages == parent_pages",
    )); // CoW: same pages
    ctx.push_obligation(ProofObligation::assume(
        "ppu_def",
        "physical_pages_used == parent_pages",
    )); // no new allocation
    ctx.push_obligation(ProofObligation::assert("same", "child_pages == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "no_extra",
        "physical_pages_used == parent_pages",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fork: child shares parent's 500 pages, 0 new allocs",
    );
}

#[test]
fn cow_fault_handler_cost() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "page_copy_cycles",
        "pte_update_cycles",
        "tlb_flush_cycles",
        "total_fault_cost",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pcc", "page_copy_cycles == 4000"));
    ctx.push_obligation(ProofObligation::assume("puc", "pte_update_cycles == 100"));
    ctx.push_obligation(ProofObligation::assume("tfc", "tlb_flush_cycles == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "tfc_def",
        "total_fault_cost == page_copy_cycles + pte_update_cycles + tlb_flush_cycles",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4300",
        "total_fault_cost == 4300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoW fault: 4000 + 100 + 200 = 4300 cycles");
}

#[test]
fn dirty_page_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["total_shared", "dirtied", "ratio_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ts", "total_shared == 500"));
    ctx.push_obligation(ProofObligation::assume("d", "dirtied == 50")); // 10% written after fork
    ctx.push_obligation(ProofObligation::assume(
        "rp_def",
        "ratio_pct == dirtied * 100 / total_shared",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "ratio_pct == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "dirty ratio: 50/500 = 10%");
}

#[test]
fn deduplication_candidates() {
    let mut ctx = VerificationContext::new();
    for v in &["total_pages", "distinct_content", "duplicates"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tp", "total_pages == 10000"));
    ctx.push_obligation(ProofObligation::assume("dc", "distinct_content == 7000"));
    ctx.push_obligation(ProofObligation::assume(
        "dup_def",
        "duplicates == total_pages - distinct_content",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3000", "duplicates == 3000"));
    ctx.push_obligation(ProofObligation::assert("positive", "duplicates > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dedup: 10000 - 7000 = 3000 duplicate pages");
}
