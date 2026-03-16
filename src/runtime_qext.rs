/// Generic runtime quadratic extension field element.
///
/// RuntimeQExt<FV, R, F> represents an element of SpecQuadExt<FV, R>
/// where F is the runtime base field type implementing RuntimeFieldOps<FV>.
///
/// This generalizes RuntimeQExtRat<R> (which is hardcoded to RuntimeRational/Rational)
/// to support arbitrary base fields, enabling nested extensions:
///   Level 0: RuntimeRational                              (Rational)
///   Level 1: RuntimeQExt<Rational, R1, RuntimeRational>   (SpecQuadExt<Rational, R1>)
///   Level 2: RuntimeQExt<QExt1, R2, RtQExt1>             (SpecQuadExt<QExt1, R2>)
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
use crate::radicand::Radicand;
#[cfg(verus_keep_ghost)]
use crate::radicand::PositiveRadicand;
#[cfg(verus_keep_ghost)]
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use crate::ordered::*;
#[cfg(verus_keep_ghost)]
use crate::runtime_field::RuntimeFieldOps;

#[cfg(verus_keep_ghost)]
verus! {

// ═══════════════════════════════════════════════════════════════════
//  RuntimeQExt — generic runtime quadratic extension
// ═══════════════════════════════════════════════════════════════════

/// Runtime element of a quadratic extension F(√d).
///
/// Stores re + im·√d where:
///   - F is the runtime base field type (e.g., RuntimeRational or another RuntimeQExt)
///   - FV is the spec-level base field (e.g., Rational or SpecQuadExt<...>)
///   - R is the radicand witness type
///   - radicand_rt is the runtime value of the radicand d
///
/// Unlike RuntimeQExtRat, this doesn't use RuntimeRadicand<R> for the radicand.
/// Instead, the radicand is stored in the struct and validated by wf_spec.
pub struct RuntimeQExt<FV: OrderedField, R: Radicand<FV>, F: RuntimeFieldOps<FV>> {
    pub re: F,
    pub im: F,
    pub radicand_rt: F,
    pub model: Ghost<SpecQuadExt<FV, R>>,
}

impl<FV: OrderedField, R: Radicand<FV>, F: RuntimeFieldOps<FV>> RuntimeQExt<FV, R, F> {
    /// Well-formedness: runtime components match the ghost model,
    /// and the stored radicand matches the spec-level radicand value.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.re.wf_spec()
        &&& self.im.wf_spec()
        &&& self.radicand_rt.wf_spec()
        &&& self.re.rf_view() == self.model@.re
        &&& self.im.rf_view() == self.model@.im
        &&& self.radicand_rt.rf_view() == R::value()
    }

    /// Construct from components and radicand.
    pub fn new(re: F, im: F, radicand_rt: F) -> (out: Self)
        requires
            re.wf_spec(),
            im.wf_spec(),
            radicand_rt.wf_spec(),
            radicand_rt.rf_view() == R::value(),
        ensures
            out.wf_spec(),
            out.model@.re == re.rf_view(),
            out.model@.im == im.rf_view(),
    {
        let ghost model = qext::<FV, R>(re.rf_view(), im.rf_view());
        RuntimeQExt { re, im, radicand_rt, model: Ghost(model) }
    }

    /// Embed a base field element into the extension: v ↦ v + 0·√d.
    ///
    /// Requires a radicand runtime value to populate the struct.
    /// Spec: out@ == qext_from_rational(v.rf_view())
    pub fn embed_base(v: F, radicand_rt: F) -> (out: Self)
        requires
            v.wf_spec(),
            radicand_rt.wf_spec(),
            radicand_rt.rf_view() == R::value(),
        ensures
            out.wf_spec(),
            out.model@.re == v.rf_view(),
            out.model@.im == FV::zero(),
    {
        let im = v.rf_zero_like();
        let ghost model = qext::<FV, R>(v.rf_view(), FV::zero());
        RuntimeQExt { re: v, im, radicand_rt, model: Ghost(model) }
    }

    // ─── Ring operations ─────────────────────────────────────────

    /// Addition: (a + b√d) + (c + e√d) = (a+c) + (b+e)√d
    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures
            out.wf_spec(),
            out.model@ == qe_add::<FV, R>(self.model@, rhs.model@),
    {
        let re = self.re.rf_add(&rhs.re);
        let im = self.im.rf_add(&rhs.im);
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_add::<FV, R>(self.model@, rhs.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Subtraction: (a + b√d) - (c + e√d) = (a-c) + (b-e)√d
    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures
            out.wf_spec(),
            out.model@ == qe_sub::<FV, R>(self.model@, rhs.model@),
    {
        let re = self.re.rf_sub(&rhs.re);
        let im = self.im.rf_sub(&rhs.im);
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_sub::<FV, R>(self.model@, rhs.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Negation: -(a + b√d) = (-a) + (-b)√d
    pub fn neg_exec(&self) -> (out: Self)
        requires self.wf_spec()
        ensures
            out.wf_spec(),
            out.model@ == qe_neg::<FV, R>(self.model@),
    {
        let re = self.re.rf_neg();
        let im = self.im.rf_neg();
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_neg::<FV, R>(self.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Multiplication: (a + b√d)(c + e√d) = (ac + bed) + (ae + bc)√d
    pub fn mul_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures
            out.wf_spec(),
            out.model@ == qe_mul::<FV, R>(self.model@, rhs.model@),
    {
        // Real part: a*c + b*e*d
        let ac = self.re.rf_mul(&rhs.re);
        let be = self.im.rf_mul(&rhs.im);
        let bed = be.rf_mul(&self.radicand_rt);
        let re = ac.rf_add(&bed);

        // Imaginary part: a*e + b*c
        let ae = self.re.rf_mul(&rhs.im);
        let bc = self.im.rf_mul(&rhs.re);
        let im = ae.rf_add(&bc);

        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_mul::<FV, R>(self.model@, rhs.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Conjugate: (a + b√d) → (a - b√d)
    pub fn conj_exec(&self) -> (out: Self)
        requires self.wf_spec()
        ensures
            out.wf_spec(),
            out.model@ == qe_conj::<FV, R>(self.model@),
    {
        let re = self.re.rf_copy();
        let im = self.im.rf_neg();
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_conj::<FV, R>(self.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Component-wise equivalence: a.re ≡ b.re && a.im ≡ b.im
    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == qe_eqv::<FV, R>(self.model@, rhs.model@)
    {
        let re_eq = self.re.rf_eq(&rhs.re);
        let im_eq = self.im.rf_eq(&rhs.im);
        re_eq && im_eq
    }

    /// Copy by copying internal fields.
    pub fn copy_exec(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model@ == self.model@
    {
        let re = self.re.rf_copy();
        let im = self.im.rf_copy();
        let radicand = self.radicand_rt.rf_copy();
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(self.model@) }
    }

    /// Norm: a² - b²d (returns a base field element, not an extension element).
    pub fn norm_exec(&self) -> (out: F)
        requires self.wf_spec()
        ensures
            out.wf_spec(),
            out.rf_view() == qe_norm::<FV, R>(self.model@),
    {
        // a²
        let a_sq = self.re.rf_mul(&self.re);
        // b²
        let b_sq = self.im.rf_mul(&self.im);
        // b² * d
        let b_sq_d = b_sq.rf_mul(&self.radicand_rt);
        // a² - b²d
        a_sq.rf_sub(&b_sq_d)
    }

    /// Reciprocal: (a + b√d)⁻¹ = (a - b√d) / (a² - b²d)
    pub fn recip_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !qe_eqv::<FV, R>(self.model@, qe_zero::<FV, R>()),
        ensures
            out.wf_spec(),
            out.model@ == qe_recip::<FV, R>(self.model@),
    {
        let norm = self.norm_exec();

        proof {
            crate::lemmas::lemma_norm_nonzero::<FV, R>(self.model@);
        }

        let norm_inv = norm.rf_recip();

        let re = self.re.rf_mul(&norm_inv);
        let neg_im = self.im.rf_neg();
        let im = neg_im.rf_mul(&norm_inv);

        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_recip::<FV, R>(self.model@);
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    /// Division: x / y = x * y⁻¹
    pub fn div_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !qe_eqv::<FV, R>(rhs.model@, qe_zero::<FV, R>()),
        ensures
            out.wf_spec(),
            out.model@ == qe_div::<FV, R>(self.model@, rhs.model@),
    {
        let rhs_inv = rhs.recip_exec();
        self.mul_exec(&rhs_inv)
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Ordering operations (require PositiveRadicand)
// ═══════════════════════════════════════════════════════════════════

impl<FV: OrderedField, R: PositiveRadicand<FV>, F: RuntimeFieldOps<FV>> RuntimeQExt<FV, R, F> {
    /// Non-negativity check: a + b√d ≥ 0.
    pub fn nonneg_exec(&self) -> (out: bool)
        requires self.wf_spec()
        ensures out == qe_nonneg::<FV, R>(self.model@)
    {
        let zero = self.re.rf_zero_like();

        let a_nonneg = zero.rf_le(&self.re);   // 0 ≤ a
        let b_nonneg = zero.rf_le(&self.im);   // 0 ≤ b

        if a_nonneg && b_nonneg {
            return true;
        }

        // Compute a² and b²d for cases 2 and 3
        let a_sq = self.re.rf_mul(&self.re);
        let b_sq = self.im.rf_mul(&self.im);
        let b2d = b_sq.rf_mul(&self.radicand_rt);

        let zero2 = self.re.rf_zero_like();
        let b_neg = self.im.rf_lt(&zero2);     // b < 0
        let zero3 = self.re.rf_zero_like();
        let a_neg = self.re.rf_lt(&zero3);      // a < 0
        let zero4 = self.re.rf_zero_like();
        let b_pos = zero4.rf_lt(&self.im);      // 0 < b

        if a_nonneg && b_neg && b2d.rf_le(&a_sq) {
            return true;
        }

        if a_neg && b_pos && a_sq.rf_le(&b2d) {
            return true;
        }

        false
    }

    /// Less-than-or-equal: x ≤ y iff y - x ≥ 0.
    pub fn le_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == qe_le::<FV, R>(self.model@, rhs.model@)
    {
        let diff = rhs.sub_exec(self);
        diff.nonneg_exec()
    }

    /// Strict less-than: x < y iff x ≤ y and x ≢ y.
    pub fn lt_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == qe_lt::<FV, R>(self.model@, rhs.model@)
    {
        let le = self.le_exec(rhs);
        let eq = self.eq_exec(rhs);
        le && !eq
    }
}

// ═══════════════════════════════════════════════════════════════════
//  RuntimeFieldOps implementation for RuntimeQExt
// ═══════════════════════════════════════════════════════════════════

impl<FV: OrderedField, R: PositiveRadicand<FV>, F: RuntimeFieldOps<FV>>
    RuntimeFieldOps<SpecQuadExt<FV, R>> for RuntimeQExt<FV, R, F>
{
    open spec fn rf_view(&self) -> SpecQuadExt<FV, R> {
        self.model@
    }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool {
        self.wf_spec()
    }

    fn rf_add(&self, rhs: &Self) -> (out: Self) {
        self.add_exec(rhs)
    }

    fn rf_sub(&self, rhs: &Self) -> (out: Self) {
        self.sub_exec(rhs)
    }

    fn rf_neg(&self) -> (out: Self) {
        self.neg_exec()
    }

    fn rf_mul(&self, rhs: &Self) -> (out: Self) {
        self.mul_exec(rhs)
    }

    fn rf_eq(&self, rhs: &Self) -> (out: bool) {
        self.eq_exec(rhs)
    }

    fn rf_le(&self, rhs: &Self) -> (out: bool) {
        self.le_exec(rhs)
    }

    fn rf_lt(&self, rhs: &Self) -> (out: bool) {
        self.lt_exec(rhs)
    }

    fn rf_recip(&self) -> (out: Self) {
        self.recip_exec()
    }

    fn rf_div(&self, rhs: &Self) -> (out: Self) {
        self.div_exec(rhs)
    }

    fn rf_copy(&self) -> (out: Self) {
        self.copy_exec()
    }

    fn rf_zero_like(&self) -> (out: Self) {
        let re = self.re.rf_zero_like();
        let im = self.re.rf_zero_like();
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_zero::<FV, R>();
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    fn rf_one_like(&self) -> (out: Self) {
        let re = self.re.rf_one_like();
        let im = self.re.rf_zero_like();
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qe_one::<FV, R>();
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }

    open spec fn spec_embed_rational(v: Rational) -> SpecQuadExt<FV, R> {
        qext::<FV, R>(F::spec_embed_rational(v), FV::zero())
    }

    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self) {
        let re = self.re.rf_embed_rational(v);
        let im = self.re.rf_zero_like();
        let radicand = self.radicand_rt.rf_copy();
        let ghost model = qext::<FV, R>(F::spec_embed_rational(v@), FV::zero());
        RuntimeQExt { re, im, radicand_rt: radicand, model: Ghost(model) }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Type aliases for common tower levels
// ═══════════════════════════════════════════════════════════════════

/// Level 1 runtime extension: RuntimeRational components over Rational.
pub type RuntimeQExtL1<R> = RuntimeQExt<Rational, R, RuntimeRational>;

// ─── Dynamic tower runtime type aliases ──────────────────────────

/// Runtime level-1 dynamic extension: elements of ℚ(√d₁)
pub type RuntimeDynL1 = RuntimeQExt<Rational, crate::instances::DynRadicand1, RuntimeRational>;

/// Runtime level-2 dynamic extension: elements of ℚ(√d₁)(√d₂)
pub type RuntimeDynL2 = RuntimeQExt<
    crate::instances::DynLevel1,
    crate::instances::DynRadicand2,
    RuntimeDynL1,
>;

/// Runtime level-3 dynamic extension: elements of ℚ(√d₁)(√d₂)(√d₃)
pub type RuntimeDynL3 = RuntimeQExt<
    crate::instances::DynLevel2,
    crate::instances::DynRadicand3,
    RuntimeDynL2,
>;

} // verus!
