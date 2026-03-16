/// RuntimeFieldOps: exec-level trait for generic field arithmetic.
///
/// Models after ExecRing<R> in verus-cutedsl/src/runtime/scan.rs.
/// Provides the arithmetic operations needed to write generic code
/// over runtime field types (RuntimeRational, RuntimeQExt, etc.).
///
/// The trait is parameterized by the spec-level type V: OrderedField.
/// Each exec type maps to a unique V via rf_view.
use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::equivalence::Equivalence;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::additive_group::AdditiveGroup;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ring::Ring;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::partial_order::PartialOrder;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ordered_ring::OrderedRing;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::Field;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
verus! {

// Re-export RationalModel for convenience
pub type RationalModel = Rational;

/// Exec-level trait for runtime field arithmetic.
///
/// Provides generic arithmetic operations that bridge to spec-level
/// OrderedField operations. Each implementing type maps to a specific
/// spec type V via rf_view.
///
/// "Like" construction methods (rf_zero_like, rf_one_like) take &self
/// to allow copying internal context (e.g., radicand values) that
/// may be needed by extension field types.
pub trait RuntimeFieldOps<V: OrderedField>: Sized {
    /// Map this runtime element to its spec-level counterpart.
    spec fn rf_view(&self) -> V;

    /// Well-formedness: runtime fields match the ghost model.
    spec fn wf_spec(&self) -> bool;

    // ─── Ring operations ─────────────────────────────────────────

    fn rf_add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().add(rhs.rf_view());

    fn rf_sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().sub(rhs.rf_view());

    fn rf_neg(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().neg();

    fn rf_mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().mul(rhs.rf_view());

    // ─── Equivalence and ordering ────────────────────────────────

    fn rf_eq(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().eqv(rhs.rf_view());

    fn rf_le(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().le(rhs.rf_view());

    fn rf_lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().lt(rhs.rf_view());

    // ─── Field operations ────────────────────────────────────────

    fn rf_recip(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !self.rf_view().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.rf_view() == self.rf_view().recip();

    fn rf_div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs.rf_view().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.rf_view() == self.rf_view().div(rhs.rf_view());

    // ─── Copy and construction ───────────────────────────────────

    fn rf_copy(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view();

    /// Create zero with the same context (radicand, etc.) as self.
    fn rf_zero_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == V::zero();

    /// Create one with the same context as self.
    fn rf_one_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == V::one();

    // ─── Embedding from Rational ────────────────────────────────

    /// Spec-level canonical embedding from Rational into V.
    ///
    /// For V = Rational: identity.
    /// For V = SpecQuadExt<FV, R>: qext_from_rational(FV::spec_embed_rational(v)).
    spec fn spec_embed_rational(v: Rational) -> V;

    /// Embed a rational value into this field, using self for context
    /// (radicand, etc.).
    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self)
        requires self.wf_spec(), v.wf_spec()
        ensures out.wf_spec(), out.rf_view() == Self::spec_embed_rational(v@);
}

// ═══════════════════════════════════════════════════════════════════
//  RuntimeFieldOps<Rational> for RuntimeRational
// ═══════════════════════════════════════════════════════════════════

impl RuntimeFieldOps<Rational> for RuntimeRational {
    #[verifier::inline]
    open spec fn rf_view(&self) -> Rational {
        self@
    }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool {
        self.wf_spec()
    }

    fn rf_add(&self, rhs: &Self) -> (out: Self) {
        self.add(rhs)
    }

    fn rf_sub(&self, rhs: &Self) -> (out: Self) {
        self.sub(rhs)
    }

    fn rf_neg(&self) -> (out: Self) {
        self.neg()
    }

    fn rf_mul(&self, rhs: &Self) -> (out: Self) {
        self.mul(rhs)
    }

    fn rf_eq(&self, rhs: &Self) -> (out: bool) {
        self.eq(rhs)
    }

    fn rf_le(&self, rhs: &Self) -> (out: bool) {
        self.le(rhs)
    }

    fn rf_lt(&self, rhs: &Self) -> (out: bool) {
        self.lt(rhs)
    }

    fn rf_recip(&self) -> (out: Self) {
        // recip() returns Option — unwrap since we require nonzero
        self.recip().unwrap()
    }

    fn rf_div(&self, rhs: &Self) -> (out: Self) {
        self.div(rhs)
    }

    fn rf_copy(&self) -> (out: Self) {
        crate::runtime::copy_rational(self)
    }

    fn rf_zero_like(&self) -> (out: Self) {
        RuntimeRational::from_int(0)
    }

    fn rf_one_like(&self) -> (out: Self) {
        RuntimeRational::from_int(1)
    }

    #[verifier::inline]
    open spec fn spec_embed_rational(v: Rational) -> Rational {
        v
    }

    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self) {
        crate::runtime::copy_rational(v)
    }
}

} // verus!
