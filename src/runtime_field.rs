///  Runtime arithmetic trait hierarchy — re-exported from verus-algebra.
///
///  The core traits live in verus_algebra::traits::runtime:
///    RuntimeRingOps<V: Ring>          — add, sub, neg, mul, eq, copy, zero, one
///    RuntimeFieldOps<V: Field>        — extends ring with recip, div
///    RuntimeOrderedFieldOps<V: OrderedField> — extends field with le, lt
///
///  The RuntimeRational impls live in verus_rational::runtime_ops.
///
///  This module adds:
///    RuntimeRationalEmbedding<V: Ring> — embed rationals into any runtime ring
///    RuntimeRational impl of embedding (identity embedding)
use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ring::Ring;
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

    fn embed_rational(&self, v: &RuntimeRational) -> (out: Self)
        requires self.wf_spec(), v.wf_spec()
        ensures out.wf_spec(), out.model() == Self::spec_embed_rational(v@);
}

//  ═══════════════════════════════════════════════════════════════════
//   RuntimeRational embedding impl (identity: Rational → Rational)
//  ═══════════════════════════════════════════════════════════════════

impl RuntimeRationalEmbedding<Rational> for RuntimeRational {
    #[verifier::inline]
    open spec fn spec_embed_rational(v: Rational) -> Rational { v }

    fn embed_rational(&self, v: &RuntimeRational) -> (out: Self) {
        verus_rational::runtime_rational::copy_rational(v)
    }
}

} //  verus!
