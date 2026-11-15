// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 ADVERSARIAL PROBES (scratch). Every `_cx` body ALWAYS divides by
// zero, so a `Verified` is a FALSE VERIFY. `_ok` must verify.

fn g1_apply(g: impl Fn(u64) -> u64, a: u64) -> u64 {
    g(a)
}

type RAliasVec = Vec<u64>;
type RAliasA1 = Vec<u64>;
type RAliasA2 = RAliasA1;

struct RWrap {
    d: Vec<u64>,
}

macro_rules! r_hidden {
    ($n:ident) => {
        let $n: Vec<u64> = Vec::new();
    };
}

macro_rules! r_hidden_ghost {
    ($n:ident) => {
        let $n: Seq<u64> = Seq::empty();
    };
}

fn r_make_seq() -> Seq<u64> {
    Seq::empty()
}

#[trust_vc::ensures(true)]
fn ra1_nested_block_cx(v: RAliasVec) {
    {
        {
            let v: Seq<u64> = Seq::empty();
            let _ = v;
        }
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra2_nested_closure_cx(v: RAliasVec) {
    let h = |_q: u64| {
        let k = |_r: u64| {
            let v: Seq<u64> = Seq::empty();
            let _ = v;
            0u64
        };
        let _ = k;
        0u64
    };
    let _ = g1_apply(h, 0u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra4_if_let_cx(v: RAliasVec) {
    if let Some(v) = Some(Seq::empty()) {
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra5_while_let_cx(v: RAliasVec) {
    while let Some(v) = None::<Seq<u64>> {
        let _ = v;
        break;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra6_loop_rebind_cx(v: RAliasVec) {
    let mut n = 0u64;
    loop {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
        n = n + 1;
        if n > 0 {
            break;
        }
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra7_init_is_call_cx(v: RAliasVec) {
    {
        let v = r_make_seq();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra8_init_is_qualified_call_cx(v: RAliasVec) {
    {
        let v = <Seq<u64>>::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra9_let_else_cx(v: RAliasVec) {
    let Some(v) = Some(Seq::empty()) else {
        return;
    };
    let _ = v;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra10_const_item_shadow_cx(v: RAliasVec) {
    {
        const v: u64 = 0u64;
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RA3 the ghost binder hidden in a MACRO: the collector cannot see it, so the
// alias parameter must stay UNRESOLVED and be checked.
#[trust_vc::ensures(true)]
fn ra3_macro_hidden_ghost_let_cx(v: RAliasVec) {
    {
        r_hidden_ghost!(v);
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RA3B THE DANGEROUS DIRECTION: an EXEC rebind hidden in a macro over a
// DECLARED SPEC parameter. Nothing expands the macro, so the binder is
// invisible and the parameter's ghost reading keeps answering.
#[trust_vc::ensures(true)]
fn ra3b_macro_hidden_exec_rebind_cx(s: Seq<u64>) {
    r_hidden!(s);
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RA3C THE DECISIVE CONTROL: the same rebind written LITERALLY.
#[trust_vc::ensures(true)]
fn ra3c_literal_exec_rebind_cx(s: Seq<u64>) {
    let s: Vec<u64> = Vec::new();
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RA3D the same as RA3B with NO macro at all: the spec receiver is genuinely
// spec, so this one is the liar twin and must VERIFY on an honest body.
#[trust_vc::ensures(true)]
fn ra3d_plain_spec_receiver_ok(s: Seq<u64>) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb1_nested_at_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (r @ v, _z) = p;
    let _ = q;
    let _ = r;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb2_at_on_slice_cx(v: Seq<u64>, arr: [Vec<u64>; 2]) {
    let q @ [v, _z] = arr;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb3_at_on_struct_pattern_cx(v: Seq<u64>, w: RWrap) {
    let q @ RWrap { d: v } = w;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb4_at_on_reference_pattern_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ &(v, _z) = &p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb5_at_or_subpattern_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ ((v, _z) | (v, _z)) = p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb6_at_under_type_ascription_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let (q @ (v, _z)): (Vec<u64>, u64) = p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb7_at_ref_binding_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (ref v, _z) = p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd1_slice_ref_cx(v: &[u64]) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd1_slice_refb_control_cx(v: &[u64]) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd2_option_vec_cx(v: Option<Vec<u64>>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd2_option_vecb_control_cx(v: Option<Vec<u64>>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd3_hashmap_cx(v: HashMap<u64, u64>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map_values(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd3_hashmapb_control_cx(v: HashMap<u64, u64>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map_values(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd4_box_vec_cx(v: Box<Vec<u64>>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd4_box_vecb_control_cx(v: Box<Vec<u64>>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd6_impl_iterator_cx(v: impl Iterator<Item = u64>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd6_impl_iteratorb_control_cx(v: impl Iterator<Item = u64>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd7_nested_vec_cx(v: Vec<Vec<u64>>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd7_nested_vecb_control_cx(v: Vec<Vec<u64>>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd8_array_cx(v: [u64; 3]) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd8_arrayb_control_cx(v: [u64; 3]) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd9_double_alias_cx(v: RAliasA2) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd9_double_aliasb_control_cx(v: RAliasA2) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd10_fully_qualified_cx(v: std::vec::Vec<u64>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd10_fully_qualifiedb_control_cx(v: std::vec::Vec<u64>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd11_vecdeque_cx(v: VecDeque<u64>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd11_vecdequeb_control_cx(v: VecDeque<u64>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd12_user_struct_cx(v: RWrap) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd12_user_structb_control_cx(v: RWrap) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd13_tuple_param_cx(v: (Vec<u64>, u64)) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd13_tuple_paramb_control_cx(v: (Vec<u64>, u64)) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd14_ref_alias_cx(v: &RAliasVec) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd14_ref_aliasb_control_cx(v: &RAliasVec) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd15_binary_heap_cx(v: BinaryHeap<u64>) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd15_binary_heapb_control_cx(v: BinaryHeap<u64>) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd5_generic_param_cx<T>(v: T) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd5b_generic_param_control_cx<T>(v: T) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ---- NO-SINK TWINS: the same closure literal, handed to NOTHING ----

#[trust_vc::ensures(true)]
fn ra1_nested_block_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra2_nested_closure_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra3b_macro_hidden_exec_rebind_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra4_if_let_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra5_while_let_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra6_loop_rebind_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra7_init_is_call_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra8_init_is_qualified_call_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra9_let_else_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ra10_const_item_shadow_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb1_nested_at_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb2_at_on_slice_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb3_at_on_struct_pattern_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb4_at_on_reference_pattern_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb5_at_or_subpattern_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb6_at_under_type_ascription_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rb7_at_ref_binding_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd1_slice_ref_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd2_option_vec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd3_hashmap_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd4_box_vec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd6_impl_iterator_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd7_nested_vec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd8_array_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd9_double_alias_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd10_fully_qualified_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd11_vecdeque_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd12_user_struct_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd13_tuple_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd14_ref_alias_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd15_binary_heap_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rd5_generic_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
