///  Runtime arithmetic trait hierarchy — re-exported from verus-algebra.
///
///  The core traits live in verus_algebra::traits::runtime:
///    RuntimeRingOps<V: Ring>          — add, sub, neg, mul, eq, copy, zero, one
///    RuntimeFieldOps<V: Field>        — extends ring with recip, div
///    RuntimeOrderedFieldOps<V: OrderedField> — extends field with le, lt
///
///  This module adds:
///    RuntimeRationalEmbedding<V: Ring> — embed rationals into any runtime ring
///    RuntimeRational impls for all three levels + embedding
use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::equivalence::Equivalence;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ring::Ring;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::Field;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
pub use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
verus! {

//  Re-export RationalModel for convenience
pub type RationalModel = Rational;

//  ═══════════════════════════════════════════════════════════════════
//   Rational embedding extension trait
//  ═══════════════════════════════════════════════════════════════════

///  Embed rational numbers into any runtime ring type.
///  Separated from RuntimeRingOps to avoid a verus-rational dependency
///  in verus-algebra.
pub trait RuntimeRationalEmbedding<V: Ring>: RuntimeRingOps<V> {
    spec fn spec_embed_rational(v: Rational) -> V;

    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self)
        requires self.wf_spec(), v.wf_spec()
        ensures out.wf_spec(), out.rf_view() == Self::spec_embed_rational(v@);
}

//  ═══════════════════════════════════════════════════════════════════
//   RuntimeRational: implements all levels + embedding
//  ═══════════════════════════════════════════════════════════════════

impl RuntimeRingOps<Rational> for RuntimeRational {
    #[verifier::inline]
    open spec fn rf_view(&self) -> Rational { self@ }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool { self.wf_spec() }

    fn rf_add(&self, rhs: &Self) -> (out: Self) { self.add(rhs) }
    fn rf_sub(&self, rhs: &Self) -> (out: Self) { self.sub(rhs) }
    fn rf_neg(&self) -> (out: Self) { self.neg() }
    fn rf_mul(&self, rhs: &Self) -> (out: Self) { self.mul(rhs) }
    fn rf_eq(&self, rhs: &Self) -> (out: bool) { self.eq(rhs) }
    fn rf_copy(&self) -> (out: Self) { crate::runtime::copy_rational(self) }
    fn rf_zero_like(&self) -> (out: Self) { RuntimeRational::from_int(0) }
    fn rf_one_like(&self) -> (out: Self) { RuntimeRational::from_int(1) }
}

impl RuntimeFieldOps<Rational> for RuntimeRational {
    fn rf_recip(&self) -> (out: Self) { self.recip().unwrap() }
    fn rf_div(&self, rhs: &Self) -> (out: Self) { self.div(rhs) }
}

impl RuntimeOrderedFieldOps<Rational> for RuntimeRational {
    fn rf_le(&self, rhs: &Self) -> (out: bool) { self.le(rhs) }
    fn rf_lt(&self, rhs: &Self) -> (out: bool) { self.lt(rhs) }
}

impl RuntimeRationalEmbedding<Rational> for RuntimeRational {
    #[verifier::inline]
    open spec fn spec_embed_rational(v: Rational) -> Rational { v }

    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self) {
        crate::runtime::copy_rational(v)
    }
}

} //  verus!
