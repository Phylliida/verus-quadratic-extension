use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::partial_order::PartialOrder;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::determinant;
use crate::radicand::Radicand;
use crate::radicand::PositiveRadicand;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Non-negativity predicate for quadratic extension elements
// ═══════════════════════════════════════════════════════════════════

/// Non-negativity of a + b√d (where d > 0, choosing the positive root).
///
/// An element a + b√d is non-negative iff:
///   - both a >= 0 and b >= 0 (trivially non-negative), or
///   - a >= 0, b < 0, and b²d <= a² (a dominates the negative b√d term), or
///   - a < 0, b > 0, and a² <= b²d (b√d dominates the negative a term).
///
/// This uses the fact that for d > 0, we have √d > 0, so sign(b√d) = sign(b).
pub open spec fn qe_nonneg<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
) -> bool {
    let a = x.re;
    let b = x.im;
    let d = R::value();
    let a2 = a.mul(a);
    let b2d = b.mul(b).mul(d);
    // Case 1: both non-negative
    (F::zero().le(a) && F::zero().le(b))
    // Case 2: a non-negative, b negative, a² dominates b²d
    || (F::zero().le(a) && b.lt(F::zero()) && b2d.le(a2))
    // Case 3: a negative, b positive, b²d dominates a²
    || (a.lt(F::zero()) && F::zero().lt(b) && a2.le(b2d))
}

/// Ordering on the quadratic extension: x <= y iff y - x is non-negative.
pub open spec fn qe_le<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> bool {
    qe_nonneg::<F, R>(qe_sub::<F, R>(y, x))
}

/// Strict ordering on the quadratic extension.
pub open spec fn qe_lt<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> bool {
    qe_le::<F, R>(x, y) && !qe_eqv::<F, R>(x, y)
}

// ═══════════════════════════════════════════════════════════════════
//  Helper: qe_nonneg(0) — zero is non-negative
// ═══════════════════════════════════════════════════════════════════

/// The zero element (0 + 0√d) is non-negative.
proof fn lemma_zero_nonneg<F: OrderedField, R: PositiveRadicand<F>>()
    ensures
        qe_nonneg::<F, R>(qe_zero::<F, R>()),
{
    // Both components are F::zero(), which is <= itself.
    F::axiom_le_reflexive(F::zero());
}

// ═══════════════════════════════════════════════════════════════════
//  Helper: sub_self_eqv_zero — x - x components are eqv to zero
// ═══════════════════════════════════════════════════════════════════

/// For any x, x - x has components equivalent to zero.
proof fn lemma_sub_self_components<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    ensures
        x.re.sub(x.re).eqv(F::zero()),
        x.im.sub(x.im).eqv(F::zero()),
{
    additive_group_lemmas::lemma_sub_self::<F>(x.re);
    additive_group_lemmas::lemma_sub_self::<F>(x.im);
}

/// x - x is non-negative (needed for le_reflexive).
proof fn lemma_sub_self_nonneg<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    ensures
        qe_nonneg::<F, R>(qe_sub::<F, R>(x, x)),
{
    let diff = qe_sub::<F, R>(x, x);
    // diff.re = x.re - x.re, diff.im = x.im - x.im
    // Both are eqv to zero.
    lemma_sub_self_components::<F, R>(x);

    // 0 <= 0
    F::axiom_le_reflexive(F::zero());

    // Establish 0.eqv(0) and 0.eqv(diff.re/im) for le_congruence
    F::axiom_eqv_reflexive(F::zero());
    F::axiom_eqv_symmetric(diff.re, F::zero());
    // Now: F::zero().eqv(diff.re)
    // le_congruence: a1≡a2, b1≡b2, a1<=b1 → a2<=b2
    // With a1=0, a2=0, b1=0, b2=diff.re: 0≡0, 0≡diff.re, 0<=0 → 0<=diff.re
    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), diff.re);

    // Similarly for diff.im
    F::axiom_eqv_symmetric(diff.im, F::zero());
    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), diff.im);

    // Now we have F::zero().le(diff.re) && F::zero().le(diff.im)
    // → case 1 of qe_nonneg
}

// ═══════════════════════════════════════════════════════════════════
//  Helper: le_congruence for qe_nonneg through sub_congruence
// ═══════════════════════════════════════════════════════════════════

/// If a1 ≡ a2, b1 ≡ b2, and nonneg(b1 - a1), then nonneg(b2 - a2).
///
/// This follows because:
///   (b1 - a1).re = b1.re - a1.re ≡ b2.re - a2.re = (b2 - a2).re
///   (b1 - a1).im = b1.im - a1.im ≡ b2.im - a2.im = (b2 - a2).im
/// and all the F-level comparisons in qe_nonneg are preserved by F's le_congruence.
proof fn lemma_nonneg_congruence<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
)
    requires
        x.re.eqv(y.re),
        x.im.eqv(y.im),
        qe_nonneg::<F, R>(x),
    ensures
        qe_nonneg::<F, R>(y),
{
    let ax = x.re;
    let bx = x.im;
    let ay = y.re;
    let by = y.im;
    let d = R::value();

    // Establish congruences for derived quantities
    // ax² ≡ ay²
    ring_lemmas::lemma_mul_congruence::<F>(ax, ay, ax, ay);
    // bx² ≡ by²
    ring_lemmas::lemma_mul_congruence::<F>(bx, by, bx, by);
    // bx²·d ≡ by²·d
    F::axiom_mul_congruence_left(bx.mul(bx), by.mul(by), d);

    let ax2 = ax.mul(ax);
    let bx2d = bx.mul(bx).mul(d);
    let ay2 = ay.mul(ay);
    let by2d = by.mul(by).mul(d);

    // Transfer le/lt facts using F's congruence
    if F::zero().le(ax) && F::zero().le(bx) {
        // Case 1: both nonneg
        // 0 <= ax and ax ≡ ay → 0 <= ay
        F::axiom_eqv_reflexive(F::zero());
        F::axiom_le_congruence(F::zero(), F::zero(), ax, ay);
        F::axiom_le_congruence(F::zero(), F::zero(), bx, by);
    } else if F::zero().le(ax) && bx.lt(F::zero()) && bx2d.le(ax2) {
        // Case 2: a nonneg, b neg, b²d <= a²
        F::axiom_eqv_reflexive(F::zero());
        F::axiom_le_congruence(F::zero(), F::zero(), ax, ay);

        // bx < 0 and bx ≡ by → by < 0
        // lt_iff: bx < 0 iff bx <= 0 && !bx.eqv(0)
        F::axiom_lt_iff_le_and_not_eqv(bx, F::zero());
        F::axiom_le_congruence(bx, by, F::zero(), F::zero());
        // !bx.eqv(0) → !by.eqv(0)
        // If by.eqv(0) then bx.eqv(0) by transitivity with bx≡by — contradiction
        if by.eqv(F::zero()) {
            F::axiom_eqv_symmetric(bx, by);
            F::axiom_eqv_transitive(bx, by, F::zero());
            // contradiction: bx.eqv(0) but !bx.eqv(0)
        }
        F::axiom_lt_iff_le_and_not_eqv(by, F::zero());

        // bx2d <= ax2 and congruences → by2d <= ay2
        F::axiom_le_congruence(bx2d, by2d, ax2, ay2);
    } else {
        // Case 3: a neg, b pos, a² <= b²d
        // ax < 0, bx > 0, ax2 <= bx2d
        F::axiom_eqv_reflexive(F::zero());

        // ax < 0 and ax ≡ ay → ay < 0
        F::axiom_lt_iff_le_and_not_eqv(ax, F::zero());
        F::axiom_le_congruence(ax, ay, F::zero(), F::zero());
        if ay.eqv(F::zero()) {
            F::axiom_eqv_symmetric(ax, ay);
            F::axiom_eqv_transitive(ax, ay, F::zero());
        }
        F::axiom_lt_iff_le_and_not_eqv(ay, F::zero());

        // 0 < bx → 0 < by
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), bx);
        F::axiom_le_congruence(F::zero(), F::zero(), bx, by);
        if F::zero().eqv(by) {
            F::axiom_eqv_symmetric(bx, by);
            // 0.eqv(by) + by.eqv(bx) → 0.eqv(bx) — contradiction with !0.eqv(bx)
            F::axiom_eqv_transitive(F::zero(), by, bx);
        }
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), by);

        // ax2 <= bx2d → ay2 <= by2d
        F::axiom_le_congruence(ax2, ay2, bx2d, by2d);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  PartialOrder implementation
// ═══════════════════════════════════════════════════════════════════

impl<F: OrderedField, R: PositiveRadicand<F>> PartialOrder for SpecQuadExt<F, R> {
    open spec fn le(self, other: Self) -> bool {
        qe_le::<F, R>(self, other)
    }

    // ── Reflexivity: a <= a ──────────────────────────────────────────
    // le(a, a) = nonneg(a - a) = nonneg((0, 0)) which is case 1.

    proof fn axiom_le_reflexive(a: Self) {
        lemma_sub_self_nonneg::<F, R>(a);
    }

    // ── Antisymmetry: a <= b && b <= a → a ≡ b ────────────────────
    // nonneg(b - a) && nonneg(a - b).
    // Components of (a - b) = -(b - a), so the two conditions together
    // force both re and im differences to be zero.
    //
    // This is a case analysis: if re-diff > 0, then a-b has re < 0,
    // and similarly for im, leading to contradictions in most cases.
    // Uses the fact that for d > 0, nonneg(x) && nonneg(-x) → x ≡ 0.

    #[verifier::rlimit(40)]
    proof fn axiom_le_antisymmetric(a: Self, b: Self) {
        // Let diff = b - a, neg_diff = a - b
        let diff = qe_sub::<F, R>(b, a);
        let neg_diff = qe_sub::<F, R>(a, b);
        let d = R::value();

        // diff.re = b.re - a.re, neg_diff.re = a.re - b.re
        // diff.im = b.im - a.im, neg_diff.im = a.im - b.im

        // neg_diff.re ≡ -(diff.re) and neg_diff.im ≡ -(diff.im)
        // by sub_antisymmetric: a - b ≡ -(b - a)
        additive_group_lemmas::lemma_sub_antisymmetric::<F>(a.re, b.re);
        additive_group_lemmas::lemma_sub_antisymmetric::<F>(a.im, b.im);

        // We have qe_nonneg(diff) and qe_nonneg(neg_diff).
        // We need to show diff.re ≡ 0 and diff.im ≡ 0 (which gives b.re - a.re ≡ 0, etc.)

        // Use F's trichotomy on diff.re and diff.im vs 0
        ordered_ring_lemmas::lemma_trichotomy::<F>(F::zero(), diff.re);
        ordered_ring_lemmas::lemma_trichotomy::<F>(F::zero(), diff.im);

        // We'll show both must be eqv to zero.
        // Strategy: if diff.re > 0, then neg_diff.re < 0 (since neg_diff.re ≡ -diff.re).
        // Similarly for diff.im. Then examine what qe_nonneg(neg_diff) forces.

        // Helper: 0 ≤ diff.re iff neg_diff.re ≤ 0
        // (since neg_diff.re ≡ -diff.re and 0≤a iff -a≤0)
        ordered_ring_lemmas::lemma_neg_nonneg_iff::<F>(diff.re);
        // neg_diff.re ≡ -(diff.re), so neg_diff.re ≤ 0 iff diff.re.neg() ≤ 0
        // which iff 0 ≤ diff.re
        // So: 0 ≤ diff.re implies neg_diff.re ≤ 0 after congruence.

        // First, if diff.re.eqv(F::zero()) && diff.im.eqv(F::zero()), done:
        if diff.re.eqv(F::zero()) && diff.im.eqv(F::zero()) {
            // b.re - a.re ≡ 0 → b.re ≡ a.re, similarly for im
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<F>(b.re, a.re);
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<F>(b.im, a.im);
            // eqv is symmetric
            F::axiom_eqv_symmetric(b.re, a.re);
            F::axiom_eqv_symmetric(b.im, a.im);
            return;
        }

        // Otherwise, we need to derive a contradiction.
        // nonneg(diff) and nonneg(neg_diff) where diff ≢ 0 is impossible.
        // This is essentially: in an ordered field with d > 0,
        // a + b√d ≥ 0 and -(a + b√d) ≥ 0 implies a + b√d = 0.

        // This requires case analysis. Use assume(false) for now.
        // Proof strategy: enumerate all 9 combinations of sign(diff.re) × sign(diff.im)
        // and show each non-zero case leads to contradiction with both nonneg conditions.
        assume(false);
    }

    // ── Transitivity: a <= b && b <= c → a <= c ──────────────────
    // nonneg(b - a) && nonneg(c - b) → nonneg(c - a).
    // Since c - a = (c - b) + (b - a) component-wise,
    // this reduces to showing nonneg is closed under addition.
    //
    // Proof strategy: case-split on the three nonneg cases for each operand,
    // giving 9 combinations. Many are easy (e.g., both case 1 → case 1 for sum).
    // The hard cases involve mixed signs and need b²d comparisons with a².
    // Substantial case analysis (~200 lines).

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {
        // nonneg(b - a) && nonneg(c - b) → nonneg((c - b) + (b - a))
        // and (c - b) + (b - a) has components that telescope to c - a.

        // First establish that (c-b).re + (b-a).re ≡ (c-a).re, etc.
        // (c.re - b.re) + (b.re - a.re) ≡ c.re - a.re by sub-add-telescope
        // Similarly for im.

        // This is a substantial proof. Use assume(false).
        // Strategy: prove lemma_nonneg_add_closed, then use sub-telescope congruence.
        assume(false);
    }

    // ── Congruence: a1≡a2, b1≡b2, a1<=b1 → a2<=b2 ───────────────
    // le is defined via nonneg(b-a), so we need:
    //   nonneg(b1-a1) and (b1-a1) ≡ (b2-a2) → nonneg(b2-a2)
    // The component equivalences follow from sub_congruence.

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {
        // (b1 - a1).re = b1.re - a1.re ≡ b2.re - a2.re = (b2 - a2).re
        additive_group_lemmas::lemma_sub_congruence::<F>(b1.re, b2.re, a1.re, a2.re);
        // (b1 - a1).im = b1.im - a1.im ≡ b2.im - a2.im = (b2 - a2).im
        additive_group_lemmas::lemma_sub_congruence::<F>(b1.im, b2.im, a1.im, a2.im);

        let diff1 = qe_sub::<F, R>(b1, a1);
        let diff2 = qe_sub::<F, R>(b2, a2);

        // diff1.re ≡ diff2.re and diff1.im ≡ diff2.im
        // nonneg(diff1) → nonneg(diff2) via nonneg_congruence
        lemma_nonneg_congruence::<F, R>(diff1, diff2);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  OrderedRing implementation
// ═══════════════════════════════════════════════════════════════════

impl<F: OrderedField, R: PositiveRadicand<F>> OrderedRing for SpecQuadExt<F, R> {
    open spec fn lt(self, other: Self) -> bool {
        qe_lt::<F, R>(self, other)
    }

    // ── Totality: a <= b || b <= a ────────────────────────────────
    // Equivalent to: nonneg(b-a) || nonneg(a-b).
    // Since (a-b) = -(b-a) component-wise, this follows from
    // the fact that for any x in F(√d), either x ≥ 0 or -x ≥ 0.

    proof fn axiom_le_total(a: Self, b: Self) {
        let diff = qe_sub::<F, R>(b, a);
        let neg_diff = qe_sub::<F, R>(a, b);
        let d = R::value();

        let re = diff.re;
        let im = diff.im;

        // neg_diff.re ≡ -re, neg_diff.im ≡ -im
        additive_group_lemmas::lemma_sub_antisymmetric::<F>(a.re, b.re);
        additive_group_lemmas::lemma_sub_antisymmetric::<F>(a.im, b.im);

        // Use F's total order on components
        F::axiom_le_total(F::zero(), re);
        F::axiom_le_total(F::zero(), im);

        let re2 = re.mul(re);
        let im2d = im.mul(im).mul(d);

        // Need either nonneg(diff) or nonneg(neg_diff).
        // Case analysis on sign(re) × sign(im):

        if F::zero().le(re) && F::zero().le(im) {
            // Case 1 for diff: both nonneg → nonneg(diff)
            // Done: a <= b
        } else if re.le(F::zero()) && im.le(F::zero()) {
            // Both components non-positive → neg_diff has both nonneg
            // neg_diff.re ≡ -re >= 0, neg_diff.im ≡ -im >= 0
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(re, F::zero());
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(im, F::zero());
            // 0.neg() ≤ re.neg() and 0.neg() ≤ im.neg()
            // 0.neg() ≡ 0
            additive_group_lemmas::lemma_neg_zero::<F>();
            F::axiom_eqv_reflexive(re.neg());
            F::axiom_le_congruence(F::zero().neg(), F::zero(), re.neg(), re.neg());
            F::axiom_eqv_reflexive(im.neg());
            F::axiom_le_congruence(F::zero().neg(), F::zero(), im.neg(), im.neg());
            // Now: 0 ≤ re.neg() and 0 ≤ im.neg()
            // neg_diff.re ≡ re.neg() and neg_diff.im ≡ im.neg()
            // So nonneg(neg_diff) by case 1 after congruence
            let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
            // We've shown 0 ≤ neg_qe.re and 0 ≤ neg_qe.im
            // so nonneg(neg_qe) holds

            // Connect neg_qe to neg_diff: sub_antisymmetric gives neg_diff ≡ -diff,
            // need symmetric direction for nonneg_congruence precondition
            F::axiom_eqv_symmetric(neg_diff.re, re.neg());
            F::axiom_eqv_symmetric(neg_diff.im, im.neg());
            lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
        } else if F::zero().le(re) && im.le(F::zero()) {
            // re >= 0, im <= 0
            // For diff: need case 2 (a>=0, b<0, b²d <= a²) or not
            // For neg_diff: neg_diff.re ≡ -re <= 0, neg_diff.im ≡ -im >= 0
            //   → case 3 (a<0, b>0, a²<=b²d) might apply

            // Compare re² vs im²·d
            F::axiom_le_total(im2d, re2);

            if im2d.le(re2) {
                // b²d ≤ a² → check if case 2 applies for diff
                // Need b < 0 (i.e., im < 0, not just im ≤ 0)
                // If im ≡ 0, then case 1 applies (0 ≤ re and 0 ≤ im by congruence)
                ordered_ring_lemmas::lemma_trichotomy::<F>(im, F::zero());
                if im.eqv(F::zero()) {
                    // im ≡ 0 → 0 ≤ im
                    F::axiom_eqv_symmetric(im, F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im);
                    // Case 1 for diff
                } else {
                    // im < 0 (since im ≤ 0 and im ≢ 0)
                    F::axiom_lt_iff_le_and_not_eqv(im, F::zero());
                    // Case 2 for diff: 0≤re, im<0, im²d ≤ re²
                }
            } else {
                // re² < im²·d → case 3 for neg_diff
                // neg_diff.re ≡ -re, neg_diff.im ≡ -im
                // Need: neg_diff.re < 0 i.e. -re < 0 (true if re > 0)
                // Need: 0 < neg_diff.im i.e. 0 < -im (true if im < 0)
                // Need: neg_diff.re² ≤ neg_diff.im²·d
                //   = (-re)² ≤ (-im)²·d ≡ re² ≤ im²·d

                // neg_diff.re² ≡ re² since (-re)(-re) ≡ re·re
                ring_lemmas::lemma_neg_mul_neg::<F>(re, re);
                // neg_diff.im² ≡ im² since (-im)(-im) ≡ im·im
                ring_lemmas::lemma_neg_mul_neg::<F>(im, im);
                // neg_diff.im²·d ≡ im²·d
                F::axiom_mul_congruence_left(im.neg().mul(im.neg()), im.mul(im), d);

                // re² < im²·d (since !(im²d ≤ re²) and totality gives re² ≤ im²d)
                // But we need re²≤im²d for case 3 — we have it from totality.
                // Actually !(im2d.le(re2)) + totality doesn't directly give us re2.le(im2d)
                // because le_total gives re2.le(im2d) || im2d.le(re2), and we're in the else.
                F::axiom_le_total(re2, im2d);

                ordered_ring_lemmas::lemma_trichotomy::<F>(re, F::zero());
                ordered_ring_lemmas::lemma_trichotomy::<F>(im, F::zero());

                if re.eqv(F::zero()) && im.eqv(F::zero()) {
                    // Both zero → case 1 for diff
                    F::axiom_eqv_symmetric(im, F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im);
                } else if re.eqv(F::zero()) {
                    // re ≡ 0, im < 0 → neg_diff.im ≡ -im > 0
                    // For neg_diff (case 3): need neg_diff.re < 0
                    // But neg_diff.re ≡ -re ≡ -0 ≡ 0, so neg_diff.re is not < 0
                    // So case 3 doesn't apply. But case 1 or 2?
                    // neg_diff.re ≡ 0 ≥ 0 and neg_diff.im ≡ -im > 0 ≥ 0 → case 1
                    ordered_ring_lemmas::lemma_le_neg_flip::<F>(im, F::zero());
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_eqv_reflexive(im.neg());
                    F::axiom_le_congruence(F::zero().neg(), F::zero(), im.neg(), im.neg());

                    // neg_diff.re ≡ -re ≡ -0 ≡ 0
                    F::axiom_neg_congruence(re, F::zero());
                    F::axiom_eqv_transitive(re.neg(), F::zero().neg(), F::zero());
                    // 0 ≤ 0 ≡ neg_diff.re
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_eqv_symmetric(re.neg(), F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), re.neg());

                    let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
                    F::axiom_eqv_symmetric(neg_diff.re, re.neg());
                    F::axiom_eqv_symmetric(neg_diff.im, im.neg());
                    lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
                } else if im.eqv(F::zero()) {
                    // re > 0, im ≡ 0 → case 1: 0 ≤ re ✓, 0 ≤ im by congruence
                    F::axiom_eqv_symmetric(im, F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im);
                } else {
                    // re > 0 (since 0 ≤ re and re ≢ 0), im < 0 (since im ≤ 0 and im ≢ 0)
                    // neg_diff: re_part ≡ -re < 0, im_part ≡ -im > 0
                    // case 3: neg_diff.re < 0, 0 < neg_diff.im, neg_diff.re² ≤ neg_diff.im²·d
                    // re > 0: we have 0.le(re) and !re.eqv(0), derive !0.eqv(re)
                    if F::zero().eqv(re) {
                        F::axiom_eqv_symmetric(F::zero(), re);
                    }
                    F::axiom_lt_iff_le_and_not_eqv(F::zero(), re);
                    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(F::zero(), re);
                    // re.neg() < 0.neg() ≡ 0
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_lt_iff_le_and_not_eqv(re.neg(), F::zero().neg());
                    F::axiom_eqv_reflexive(re.neg());
                    F::axiom_le_congruence(re.neg(), re.neg(), F::zero().neg(), F::zero());
                    if re.neg().eqv(F::zero()) {
                        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
                        F::axiom_eqv_transitive(re.neg(), F::zero(), F::zero().neg());
                        // contradiction with re.neg() ≢ 0.neg()
                    }
                    F::axiom_lt_iff_le_and_not_eqv(re.neg(), F::zero());

                    // im < 0: we have im.le(0) and !im.eqv(0)
                    F::axiom_lt_iff_le_and_not_eqv(im, F::zero());
                    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(im, F::zero());
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_lt_iff_le_and_not_eqv(F::zero().neg(), im.neg());
                    F::axiom_eqv_reflexive(im.neg());
                    F::axiom_le_congruence(F::zero().neg(), F::zero(), im.neg(), im.neg());
                    if F::zero().eqv(im.neg()) {
                        // 0.neg().eqv(0) from neg_zero, 0.eqv(im.neg()) from if
                        // → 0.neg().eqv(im.neg()) by transitive — contradicts !0.neg().eqv(im.neg())
                        F::axiom_eqv_transitive(F::zero().neg(), F::zero(), im.neg());
                    }
                    F::axiom_lt_iff_le_and_not_eqv(F::zero(), im.neg());

                    // neg_qe.re² ≡ re², neg_qe.im²d ≡ im²d (shown above)
                    // re² ≤ im²d from the else branch
                    // So case 3 holds for neg_qe, then congruence to neg_diff
                    let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
                    // neg_qe.re = re.neg(), neg_qe.im = im.neg()
                    // We need neg_qe.re.mul(neg_qe.re) ≡ re.mul(re) for le transfer
                    // This is (-re)(-re) ≡ re*re, already shown
                    // And neg_qe.im.mul(neg_qe.im).mul(d) ≡ im.mul(im).mul(d), already shown
                    // Transfer: re2.le(im2d) → neg_qe.re² ≤ neg_qe.im²d via congruence
                    // neg_mul_neg gives (-x)(-x).eqv(x*x), need symmetric for le_congruence
                    F::axiom_eqv_symmetric(re.neg().mul(re.neg()), re.mul(re));
                    F::axiom_eqv_symmetric(im.neg().mul(im.neg()).mul(d), im.mul(im).mul(d));
                    F::axiom_le_congruence(
                        re2, neg_qe.re.mul(neg_qe.re),
                        im2d, neg_qe.im.mul(neg_qe.im).mul(d),
                    );
                    // neg_qe is case 3 nonneg
                    // Now transfer to neg_diff via congruence
                    F::axiom_eqv_symmetric(neg_diff.re, re.neg());
                    F::axiom_eqv_symmetric(neg_diff.im, im.neg());
                    lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
                }
            }
        } else {
            // re <= 0, im >= 0
            // Symmetric to the case above, swapping diff and neg_diff roles

            // Compare re² vs im²·d
            F::axiom_le_total(re2, im2d);

            if re2.le(im2d) {
                // a² ≤ b²d → check if case 3 applies for diff
                // Need a < 0 (i.e., re < 0)
                // Need 0 < b (i.e., 0 < im)
                ordered_ring_lemmas::lemma_trichotomy::<F>(re, F::zero());
                ordered_ring_lemmas::lemma_trichotomy::<F>(F::zero(), im);

                if re.eqv(F::zero()) {
                    // re ≡ 0 → 0 ≤ re
                    F::axiom_eqv_symmetric(re, F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), re);
                    // Case 1 for diff: 0 ≤ re and 0 ≤ im
                } else if F::zero().eqv(im) {
                    // im ≡ 0 → 0 ≤ im
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im);
                    // re ≤ 0, im ≡ 0 → neg_diff case
                    // neg_diff.re ≡ -re ≥ 0, neg_diff.im ≡ -im ≡ 0 ≥ 0 → case 1
                    ordered_ring_lemmas::lemma_le_neg_flip::<F>(re, F::zero());
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_eqv_reflexive(re.neg());
                    F::axiom_le_congruence(F::zero().neg(), F::zero(), re.neg(), re.neg());

                    // im.eqv(0) for neg_congruence (we have 0.eqv(im), need symmetric)
                    F::axiom_eqv_symmetric(F::zero(), im);
                    F::axiom_neg_congruence(im, F::zero());
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_eqv_transitive(im.neg(), F::zero().neg(), F::zero());
                    F::axiom_eqv_symmetric(im.neg(), F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im.neg());

                    let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
                    F::axiom_eqv_symmetric(neg_diff.re, re.neg());
                    F::axiom_eqv_symmetric(neg_diff.im, im.neg());
                    lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
                } else {
                    // re < 0 and 0 < im → case 3 for diff
                    F::axiom_lt_iff_le_and_not_eqv(re, F::zero());
                    F::axiom_lt_iff_le_and_not_eqv(F::zero(), im);
                }
            } else {
                // im²d < re² → case 2 for neg_diff
                // neg_diff.re ≡ -re ≥ 0, neg_diff.im ≡ -im ≤ 0
                // neg_diff.im² * d ≤ neg_diff.re²
                // where neg_diff.re² ≡ re², neg_diff.im²d ≡ im²d

                ring_lemmas::lemma_neg_mul_neg::<F>(re, re);
                ring_lemmas::lemma_neg_mul_neg::<F>(im, im);
                F::axiom_mul_congruence_left(im.neg().mul(im.neg()), im.mul(im), d);

                F::axiom_le_total(im2d, re2);

                ordered_ring_lemmas::lemma_trichotomy::<F>(re, F::zero());
                ordered_ring_lemmas::lemma_trichotomy::<F>(F::zero(), im);

                // -re ≥ 0
                ordered_ring_lemmas::lemma_le_neg_flip::<F>(re, F::zero());
                additive_group_lemmas::lemma_neg_zero::<F>();
                F::axiom_eqv_reflexive(re.neg());
                F::axiom_le_congruence(F::zero().neg(), F::zero(), re.neg(), re.neg());

                if re.eqv(F::zero()) && F::zero().eqv(im) {
                    // Both zero → case 1 for diff
                    F::axiom_eqv_symmetric(re, F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), re);
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im);
                } else if F::zero().eqv(im) {
                    // im ≡ 0 → neg_diff.im ≡ -0 ≡ 0 ≥ 0 → case 1 for neg_diff
                    F::axiom_eqv_symmetric(F::zero(), im);
                    F::axiom_neg_congruence(im, F::zero());
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_eqv_transitive(im.neg(), F::zero().neg(), F::zero());
                    F::axiom_eqv_symmetric(im.neg(), F::zero());
                    F::axiom_eqv_reflexive(F::zero());
                    F::axiom_le_reflexive(F::zero());
                    F::axiom_le_congruence(F::zero(), F::zero(), F::zero(), im.neg());

                    let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
                    F::axiom_eqv_symmetric(neg_diff.re, re.neg());
                    F::axiom_eqv_symmetric(neg_diff.im, im.neg());
                    lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
                } else {
                    // im > 0 → -im < 0
                    F::axiom_lt_iff_le_and_not_eqv(F::zero(), im);
                    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(F::zero(), im);
                    additive_group_lemmas::lemma_neg_zero::<F>();
                    F::axiom_lt_iff_le_and_not_eqv(im.neg(), F::zero().neg());
                    F::axiom_eqv_reflexive(im.neg());
                    F::axiom_le_congruence(im.neg(), im.neg(), F::zero().neg(), F::zero());
                    if im.neg().eqv(F::zero()) {
                        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
                        F::axiom_eqv_transitive(im.neg(), F::zero(), F::zero().neg());
                    }
                    F::axiom_lt_iff_le_and_not_eqv(im.neg(), F::zero());

                    // neg_diff case 2: re_neg ≥ 0, im_neg < 0, im_neg²d ≤ re_neg²
                    // im²d ≤ re² from the totality above (we're in the else of re2.le(im2d))
                    // Transfer through (-re)²≡re², (-im)²d≡im²d
                    let neg_qe: SpecQuadExt<F, R> = qext(re.neg(), im.neg());
                    // neg_mul_neg gives (-x)(-x).eqv(x*x), need symmetric for le_congruence
                    F::axiom_eqv_symmetric(im.neg().mul(im.neg()).mul(d), im.mul(im).mul(d));
                    F::axiom_eqv_symmetric(re.neg().mul(re.neg()), re.mul(re));
                    F::axiom_le_congruence(
                        im2d, neg_qe.im.mul(neg_qe.im).mul(d),
                        re2, neg_qe.re.mul(neg_qe.re),
                    );
                    F::axiom_eqv_symmetric(neg_diff.re, re.neg());
                    F::axiom_eqv_symmetric(neg_diff.im, im.neg());
                    lemma_nonneg_congruence::<F, R>(neg_qe, neg_diff);
                }
            }
        }
    }

    // ── lt iff le and not eqv ─────────────────────────────────────
    // Follows directly from the definition.

    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) {
        // qe_lt is defined as qe_le && !qe_eqv, which matches
        // a.le(b) && !a.eqv(b) by the open spec definitions.
    }

    // ── Addition preserves order: a <= b → a+c <= b+c ────────────
    // le(a, b) = nonneg(b - a)
    // le(a+c, b+c) = nonneg((b+c) - (a+c))
    // (b+c) - (a+c) components:
    //   re: (b.re+c.re) - (a.re+c.re)  which should ≡ b.re - a.re
    //   im: (b.im+c.im) - (a.im+c.im)  which should ≡ b.im - a.im
    // So the difference is congruent to (b-a), and we already have nonneg(b-a).

    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) {
        let diff_ba = qe_sub::<F, R>(b, a);
        let sum_ac = qe_add::<F, R>(a, c);
        let sum_bc = qe_add::<F, R>(b, c);
        let diff_sums = qe_sub::<F, R>(sum_bc, sum_ac);

        // We have nonneg(b - a), i.e., nonneg over the components (b.re - a.re, b.im - a.im).
        // We need nonneg((b+c) - (a+c)), i.e., nonneg over ((b.re+c.re)-(a.re+c.re), ...).
        // These component differences are congruent, so use nonneg_congruence.

        // Prove: (b.re+c.re) - (a.re+c.re) ≡ b.re - a.re
        // Use lemma_sub_pairs: (p+q) - (r+s) ≡ (p-r) + (q-s)
        // With p=b.re, q=c.re, r=a.re, s=c.re:
        //   (b.re+c.re) - (a.re+c.re) ≡ (b.re-a.re) + (c.re-c.re)
        determinant::lemma_sub_pairs::<F>(b.re, c.re, a.re, c.re);
        // c.re - c.re ≡ 0
        additive_group_lemmas::lemma_sub_self::<F>(c.re);
        // (b.re-a.re) + (c.re-c.re) ≡ (b.re-a.re) + 0
        additive_group_lemmas::lemma_add_congruence_right::<F>(
            b.re.sub(a.re), c.re.sub(c.re), F::zero(),
        );
        // (b.re-a.re) + 0 ≡ b.re-a.re
        F::axiom_add_zero_right(b.re.sub(a.re));
        // Chain: diff_sums.re ≡ (b.re-a.re)+(c.re-c.re) ≡ (b.re-a.re)+0 ≡ b.re-a.re
        F::axiom_eqv_transitive(
            diff_sums.re,
            b.re.sub(a.re).add(c.re.sub(c.re)),
            b.re.sub(a.re).add(F::zero()),
        );
        F::axiom_eqv_transitive(
            diff_sums.re,
            b.re.sub(a.re).add(F::zero()),
            b.re.sub(a.re),
        );

        // Similarly for im
        determinant::lemma_sub_pairs::<F>(b.im, c.im, a.im, c.im);
        additive_group_lemmas::lemma_sub_self::<F>(c.im);
        additive_group_lemmas::lemma_add_congruence_right::<F>(
            b.im.sub(a.im), c.im.sub(c.im), F::zero(),
        );
        F::axiom_add_zero_right(b.im.sub(a.im));
        F::axiom_eqv_transitive(
            diff_sums.im,
            b.im.sub(a.im).add(c.im.sub(c.im)),
            b.im.sub(a.im).add(F::zero()),
        );
        F::axiom_eqv_transitive(
            diff_sums.im,
            b.im.sub(a.im).add(F::zero()),
            b.im.sub(a.im),
        );

        // Now diff_sums.re ≡ diff_ba.re and diff_sums.im ≡ diff_ba.im
        // nonneg(diff_ba) → nonneg(diff_sums) via congruence
        // But nonneg_congruence takes (x, y) where x ≡ y, so we need diff_ba ≡ diff_sums direction
        // We have diff_sums.re ≡ diff_ba.re, need diff_ba.re ≡ diff_sums.re
        F::axiom_eqv_symmetric(diff_sums.re, diff_ba.re);
        F::axiom_eqv_symmetric(diff_sums.im, diff_ba.im);
        lemma_nonneg_congruence::<F, R>(diff_ba, diff_sums);
    }

    // ── Multiplication by non-negative preserves order ────────────
    // a <= b, 0 <= c, implies a*c <= b*c.
    //
    // This is the hardest axiom. It requires showing:
    //   nonneg(b - a) && nonneg(c) → nonneg(b*c - a*c)
    // where b*c - a*c = (b - a) * c in the quadratic extension.
    //
    // The proof needs: (1) mul distributes over the three nonneg cases,
    // and (2) the product of two nonneg elements is nonneg.
    // This is a substantial case analysis (~300+ lines).

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        // Proof strategy:
        // 1. Let diff = b - a. We have nonneg(diff).
        // 2. 0 <= c means nonneg(c - 0) = nonneg(c).
        // 3. b*c - a*c ≡ diff * c (by distributivity).
        // 4. Need: nonneg(diff) && nonneg(c) → nonneg(diff * c).
        // Step 4 is the hard part — product of nonneg quadratic extension elements is nonneg.
        // This requires expanding the multiplication and checking all 9 case combinations.
        assume(false);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  OrderedField implementation (marker trait, no additional axioms)
// ═══════════════════════════════════════════════════════════════════

impl<F: OrderedField, R: PositiveRadicand<F>> OrderedField for SpecQuadExt<F, R> {}

} // verus!
