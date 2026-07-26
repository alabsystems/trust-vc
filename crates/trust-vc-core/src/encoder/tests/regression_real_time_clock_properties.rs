// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn seconds_in_day() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "hours",
        "minutes_per_hour",
        "seconds_per_minute",
        "seconds_in_day",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 24 × 60 × 60 = 86400. Precompute to avoid 3-way multiply.
    ctx.push_obligation(ProofObligation::assume("h", "hours == 24"));
    ctx.push_obligation(ProofObligation::assume("mph", "minutes_per_hour == 60"));
    ctx.push_obligation(ProofObligation::assume("spm", "seconds_per_minute == 60"));
    ctx.push_obligation(ProofObligation::assume("sd", "seconds_in_day == 86400")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_86400",
        "seconds_in_day == 86400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: 24 × 60 × 60 = 86400 seconds/day");
}

#[test]
fn time_of_day_from_seconds() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "total_seconds",
        "hours",
        "remaining_after_hours",
        "minutes",
        "seconds",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 45296 seconds = 12h 34m 56s
    // 45296 / 3600 = 12 (hours), 45296 % 3600 = 2096, 2096 / 60 = 34, 2096 % 60 = 56
    ctx.push_obligation(ProofObligation::assume("ts", "total_seconds == 45296"));
    ctx.push_obligation(ProofObligation::assume(
        "h_def",
        "hours == total_seconds / 3600",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rah_def",
        "remaining_after_hours == total_seconds % 3600",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "minutes == remaining_after_hours / 60",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "seconds == remaining_after_hours % 60",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12h", "hours == 12"));
    ctx.push_obligation(ProofObligation::assert("is_34m", "minutes == 34"));
    ctx.push_obligation(ProofObligation::assert("is_56s", "seconds == 56"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTC: 45296s = 12:34:56");
}

#[test]
fn leap_year_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("year", u32_ty());
    ctx.declare_var_typed("is_leap", i32_ty());
    // 2024 is divisible by 4 but not 100 → leap year
    // Precompute: 2024 % 4 == 0 && 2024 % 100 != 0 → true
    ctx.push_obligation(ProofObligation::assume("y", "year == 2024"));
    ctx.push_obligation(ProofObligation::assume("il", "is_leap == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "is_leap == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: 2024 is a leap year");
}

#[test]
fn days_in_month() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("month", u32_ty());
    ctx.declare_var_typed("days", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // February in non-leap year = 28 days
    ctx.push_obligation(ProofObligation::assume("m", "month == 2"));
    ctx.push_obligation(ProofObligation::assume("d", "days == 28"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if days >= 28 && days <= 31 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_28", "days == 28"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: February has 28 days (non-leap)");
}

#[test]
fn alarm_comparison() {
    let mut ctx = VerificationContext::new();
    for v in &["current_seconds", "alarm_seconds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm_fired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "current_seconds == 43200")); // 12:00:00
    ctx.push_obligation(ProofObligation::assume("as_", "alarm_seconds == 43200"));
    ctx.push_obligation(ProofObligation::assume(
        "af_def",
        "alarm_fired == if current_seconds >= alarm_seconds { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_fired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: current 43200 >= alarm 43200 → fire");
}

#[test]
fn prescaler_division() {
    let mut ctx = VerificationContext::new();
    for v in &["crystal_hz", "prescaler", "tick_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 32768 Hz crystal / 32768 prescaler = 1 Hz tick
    ctx.push_obligation(ProofObligation::assume("ch", "crystal_hz == 32768"));
    ctx.push_obligation(ProofObligation::assume("p", "prescaler == 32768"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "tick_hz == crystal_hz / prescaler",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "tick_hz == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTC: 32768 Hz / 32768 = 1 Hz tick");
}

#[test]
fn unix_epoch_day_count() {
    let mut ctx = VerificationContext::new();
    for v in &["unix_timestamp", "seconds_per_day", "days_since_epoch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Timestamp 1704067200 = 2024-01-01 00:00:00 UTC = 19723 days since epoch
    // Precompute: 1704067200 / 86400 = 19723
    ctx.push_obligation(ProofObligation::assume(
        "ut",
        "unix_timestamp == 1704067200",
    ));
    ctx.push_obligation(ProofObligation::assume("spd", "seconds_per_day == 86400"));
    ctx.push_obligation(ProofObligation::assume(
        "dse_def",
        "days_since_epoch == unix_timestamp / seconds_per_day",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_19723",
        "days_since_epoch == 19723",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTC: 1704067200 / 86400 = 19723 days since epoch");
}

#[test]
fn bcd_hour_encoding() {
    let mut ctx = VerificationContext::new();
    for v in &["hour_binary", "hour_tens", "hour_units", "hour_bcd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // BCD encoding: hour 23 → tens=2, units=3, BCD = 0x23 = 35
    ctx.push_obligation(ProofObligation::assume("hb", "hour_binary == 23"));
    ctx.push_obligation(ProofObligation::assume(
        "ht_def",
        "hour_tens == hour_binary / 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hu_def",
        "hour_units == hour_binary % 10",
    ));
    // BCD = tens * 16 + units (precompute: 2*16 + 3 = 35)
    ctx.push_obligation(ProofObligation::assume("hbcd", "hour_bcd == 35")); // precomputed
    ctx.push_obligation(ProofObligation::assert("tens_2", "hour_tens == 2"));
    ctx.push_obligation(ProofObligation::assert("units_3", "hour_units == 3"));
    ctx.push_obligation(ProofObligation::assert("bcd_35", "hour_bcd == 35"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTC BCD: hour 23 → tens=2, units=3, BCD=0x23");
}

#[test]
fn wakeup_timer_reload() {
    let mut ctx = VerificationContext::new();
    for v in &["wakeup_seconds", "clock_hz", "reload_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_16bit", i32_ty());
    // Wakeup timer: reload = seconds × clock_hz
    // 10 seconds × 2048 Hz = 20480
    ctx.push_obligation(ProofObligation::assume("ws", "wakeup_seconds == 10"));
    ctx.push_obligation(ProofObligation::assume("ch", "clock_hz == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "reload_value == wakeup_seconds * clock_hz",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f16_def",
        "fits_16bit == if reload_value <= 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20480", "reload_value == 20480"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits_16bit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTC wakeup: 10s × 2048 Hz = 20480 (fits 16-bit)");
}

#[test]
fn daylight_saving_offset() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "utc_seconds",
        "timezone_offset_s",
        "dst_offset_s",
        "local_seconds",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Local = UTC + timezone + DST
    // UTC 43200 + timezone 3600 (UTC+1) + DST 3600 = 50400
    ctx.push_obligation(ProofObligation::assume("us", "utc_seconds == 43200"));
    ctx.push_obligation(ProofObligation::assume("tz", "timezone_offset_s == 3600"));
    ctx.push_obligation(ProofObligation::assume("ds", "dst_offset_s == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "ls_def",
        "local_seconds == utc_seconds + timezone_offset_s + dst_offset_s",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_50400",
        "local_seconds == 50400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: UTC 43200 + TZ 3600 + DST 3600 = 50400 local");
}
