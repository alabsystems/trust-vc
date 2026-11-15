//! Isolated bit-vector assertion data, independent of the ordinary Int query.

pub use trust_vc_bitvector::{Architecture, IntLit, Op, Query, Sort, Term};

impl From<crate::IntLit> for IntLit {
    fn from(value: crate::IntLit) -> Self {
        Self {
            negative: value.negative,
            magnitude: value.magnitude,
        }
    }
}
