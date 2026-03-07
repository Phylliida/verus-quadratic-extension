use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::field::Field;
use verus_algebra::lemmas::additive_group_lemmas;
use crate::radicand::Radicand;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  AdditiveCommutativeMonoid for SpecQuadExt<F, R>
// ═══════════════════════════════════════════════════════════════════

impl<F: Field, R: Radicand<F>> AdditiveCommutativeMonoid for SpecQuadExt<F, R> {
    open spec fn zero() -> Self {
        qe_zero::<F, R>()
    }

    open spec fn add(self, other: Self) -> Self {
        qe_add::<F, R>(self, other)
    }

    /// (a + b√d) + (c + e√d) = (c + e√d) + (a + b√d)
    proof fn axiom_add_commutative(a: Self, b: Self) {
        // Z3 unfolds qe_add, sees:
        //   re: a.re.add(b.re) vs b.re.add(a.re)
        //   im: a.im.add(b.im) vs b.im.add(a.im)
        F::axiom_add_commutative(a.re, b.re);
        F::axiom_add_commutative(a.im, b.im);
    }

    /// ((a+b√d) + (c+e√d)) + (f+g√d) = (a+b√d) + ((c+e√d) + (f+g√d))
    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        F::axiom_add_associative(a.re, b.re, c.re);
        F::axiom_add_associative(a.im, b.im, c.im);
    }

    /// (a + b√d) + (0 + 0√d) ≡ (a + b√d)
    proof fn axiom_add_zero_right(a: Self) {
        F::axiom_add_zero_right(a.re);
        F::axiom_add_zero_right(a.im);
    }

    /// a1 ≡ a2 implies a1 + c ≡ a2 + c (component-wise)
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        F::axiom_add_congruence_left(a.re, b.re, c.re);
        F::axiom_add_congruence_left(a.im, b.im, c.im);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  AdditiveGroup for SpecQuadExt<F, R>
// ═══════════════════════════════════════════════════════════════════

impl<F: Field, R: Radicand<F>> AdditiveGroup for SpecQuadExt<F, R> {
    open spec fn neg(self) -> Self {
        qe_neg::<F, R>(self)
    }

    open spec fn sub(self, other: Self) -> Self {
        qe_sub::<F, R>(self, other)
    }

    /// (a + b√d) + (-(a + b√d)) ≡ 0
    proof fn axiom_add_inverse_right(a: Self) {
        F::axiom_add_inverse_right(a.re);
        F::axiom_add_inverse_right(a.im);
    }

    /// a - b ≡ a + (-b) (component-wise)
    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        // qe_sub is defined as (a.re.sub(b.re), a.im.sub(b.im))
        // qe_add(a, qe_neg(b)) = (a.re.add(b.re.neg()), a.im.add(b.im.neg()))
        // Need: x.sub(y) ≡ x.add(y.neg()) for each component
        F::axiom_sub_is_add_neg(a.re, b.re);
        F::axiom_sub_is_add_neg(a.im, b.im);
    }

    /// a ≡ b implies -a ≡ -b
    proof fn axiom_neg_congruence(a: Self, b: Self) {
        F::axiom_neg_congruence(a.re, b.re);
        F::axiom_neg_congruence(a.im, b.im);
    }
}

} // verus!
