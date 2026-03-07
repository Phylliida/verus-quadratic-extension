use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::field::Field;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::radicand::Radicand;
use crate::spec::*;
use crate::lemmas;

verus! {

impl<F: Field, R: Radicand<F>> Ring for SpecQuadExt<F, R> {
    open spec fn one() -> Self {
        qe_one::<F, R>()
    }

    open spec fn mul(self, other: Self) -> Self {
        qe_mul::<F, R>(self, other)
    }

    // ── Commutativity ────────────────────────────────────────────────
    // (a + b√d)(c + e√d) = (c + e√d)(a + b√d)
    //
    // Real: a*c + b*e*d  vs  c*a + e*b*d
    //   → mul_comm on (a,c) and on (b,e), then congruence for b*e*d = e*b*d
    // Imag: a*e + b*c  vs  c*b + e*a
    //   → mul_comm on each term, then add_comm to swap order

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        let d = R::value();

        // Real part: a.re*b.re + a.im*b.im*d  ≡  b.re*a.re + b.im*a.im*d
        F::axiom_mul_commutative(a.re, b.re);
        F::axiom_mul_commutative(a.im, b.im);
        // a.im*b.im ≡ b.im*a.im, so a.im*b.im*d ≡ b.im*a.im*d
        F::axiom_mul_congruence_left(a.im.mul(b.im), b.im.mul(a.im), d);
        // a.re*b.re + a.im*b.im*d ≡ b.re*a.re + b.im*a.im*d
        additive_group_lemmas::lemma_add_congruence::<F>(
            a.re.mul(b.re), b.re.mul(a.re),
            a.im.mul(b.im).mul(d), b.im.mul(a.im).mul(d),
        );

        // Imaginary part: a.re*b.im + a.im*b.re  ≡  b.re*a.im + b.im*a.re
        F::axiom_mul_commutative(a.re, b.im);
        F::axiom_mul_commutative(a.im, b.re);
        // Now have: a.re*b.im ≡ b.im*a.re and a.im*b.re ≡ b.re*a.im
        // Need: a.re*b.im + a.im*b.re ≡ b.re*a.im + b.im*a.re
        additive_group_lemmas::lemma_add_congruence::<F>(
            a.re.mul(b.im), b.im.mul(a.re),
            a.im.mul(b.re), b.re.mul(a.im),
        );
        // Swap addition order: b.im*a.re + b.re*a.im ≡ b.re*a.im + b.im*a.re
        F::axiom_add_commutative(b.im.mul(a.re), b.re.mul(a.im));
        F::axiom_eqv_transitive(
            a.re.mul(b.im).add(a.im.mul(b.re)),
            b.im.mul(a.re).add(b.re.mul(a.im)),
            b.re.mul(a.im).add(b.im.mul(a.re)),
        );
    }

    // ── Associativity ────────────────────────────────────────────────
    // (x * y) * z = x * (y * z)
    //
    // This is the hardest proof. Both sides expand to the same 8-term
    // polynomial in a,b,c,e,f,g,d. We split into real and imaginary parts.

    #[verifier::rlimit(30)]
    proof fn axiom_mul_associative(x: Self, y: Self, z: Self) {
        lemmas::lemma_mul_assoc_re::<F, R>(x, y, z);
        lemmas::lemma_mul_assoc_im::<F, R>(x, y, z);
    }

    // ── Right identity: x * 1 ≡ x ──────────────────────────────────
    // (a + b√d)(1 + 0√d) = (a*1 + b*0*d) + (a*0 + b*1)√d
    //                     = a + b√d

    proof fn axiom_mul_one_right(x: Self) {
        let d = R::value();

        // Real: x.re*1 + x.im*0*d ≡ x.re
        F::axiom_mul_one_right(x.re);                      // x.re*1 ≡ x.re
        F::axiom_mul_zero_right(x.im);                     // x.im*0 ≡ 0
        F::axiom_mul_congruence_left(x.im.mul(F::zero()), F::zero(), d);
        ring_lemmas::lemma_mul_zero_left::<F>(d);           // 0*d ≡ 0
        F::axiom_eqv_transitive(x.im.mul(F::zero()).mul(d), F::zero().mul(d), F::zero());
        // x.re*1 + x.im*0*d ≡ x.re + 0
        additive_group_lemmas::lemma_add_congruence::<F>(
            x.re.mul(F::one()), x.re,
            x.im.mul(F::zero()).mul(d), F::zero(),
        );
        // x.re + 0 ≡ x.re
        F::axiom_add_zero_right(x.re);
        F::axiom_eqv_transitive(
            x.re.mul(F::one()).add(x.im.mul(F::zero()).mul(d)),
            x.re.add(F::zero()),
            x.re,
        );

        // Imaginary: x.re*0 + x.im*1 ≡ x.im
        F::axiom_mul_zero_right(x.re);                     // x.re*0 ≡ 0
        F::axiom_mul_one_right(x.im);                      // x.im*1 ≡ x.im
        additive_group_lemmas::lemma_add_congruence::<F>(
            x.re.mul(F::zero()), F::zero(),
            x.im.mul(F::one()), x.im,
        );
        // 0 + x.im ≡ x.im
        additive_group_lemmas::lemma_add_zero_left::<F>(x.im);
        F::axiom_eqv_transitive(
            x.re.mul(F::zero()).add(x.im.mul(F::one())),
            F::zero().add(x.im),
            x.im,
        );
    }

    // ── Zero annihilation: x * 0 ≡ 0 ───────────────────────────────

    proof fn axiom_mul_zero_right(x: Self) {
        let d = R::value();

        // Real: x.re*0 + x.im*0*d ≡ 0
        F::axiom_mul_zero_right(x.re);                     // x.re*0 ≡ 0
        F::axiom_mul_zero_right(x.im);                     // x.im*0 ≡ 0
        F::axiom_mul_congruence_left(x.im.mul(F::zero()), F::zero(), d);
        ring_lemmas::lemma_mul_zero_left::<F>(d);           // 0*d ≡ 0
        F::axiom_eqv_transitive(x.im.mul(F::zero()).mul(d), F::zero().mul(d), F::zero());
        additive_group_lemmas::lemma_add_congruence::<F>(
            x.re.mul(F::zero()), F::zero(),
            x.im.mul(F::zero()).mul(d), F::zero(),
        );
        // 0 + 0 ≡ 0
        F::axiom_add_zero_right(F::zero());
        F::axiom_eqv_transitive(
            x.re.mul(F::zero()).add(x.im.mul(F::zero()).mul(d)),
            F::zero().add(F::zero()),
            F::zero(),
        );

        // Imaginary: x.re*0 + x.im*0 ≡ 0
        F::axiom_mul_zero_right(x.re);
        F::axiom_mul_zero_right(x.im);
        additive_group_lemmas::lemma_add_congruence::<F>(
            x.re.mul(F::zero()), F::zero(),
            x.im.mul(F::zero()), F::zero(),
        );
        F::axiom_add_zero_right(F::zero());
        F::axiom_eqv_transitive(
            x.re.mul(F::zero()).add(x.im.mul(F::zero())),
            F::zero().add(F::zero()),
            F::zero(),
        );
    }

    // ── Left distributivity: x * (y + z) ≡ x*y + x*z ──────────────

    #[verifier::rlimit(20)]
    proof fn axiom_mul_distributes_left(x: Self, y: Self, z: Self) {
        lemmas::lemma_mul_distributes_left_re::<F, R>(x, y, z);
        lemmas::lemma_mul_distributes_left_im::<F, R>(x, y, z);
    }

    // ── Non-degeneracy: 1 ≢ 0 ───────────────────────────────────────

    proof fn axiom_one_ne_zero() {
        // one = (1, 0), zero = (0, 0)
        // If they were eqv, then 1.eqv(0) in F, contradicting F::axiom_one_ne_zero
        F::axiom_one_ne_zero();
    }

    // ── Multiplication respects equivalence on the left ─────────────

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        let d = R::value();

        // a ≡ b means a.re ≡ b.re and a.im ≡ b.im
        // Real: a.re*c.re + a.im*c.im*d  ≡  b.re*c.re + b.im*c.im*d
        F::axiom_mul_congruence_left(a.re, b.re, c.re);
        F::axiom_mul_congruence_left(a.im, b.im, c.im);
        F::axiom_mul_congruence_left(a.im.mul(c.im), b.im.mul(c.im), d);
        additive_group_lemmas::lemma_add_congruence::<F>(
            a.re.mul(c.re), b.re.mul(c.re),
            a.im.mul(c.im).mul(d), b.im.mul(c.im).mul(d),
        );

        // Imaginary: a.re*c.im + a.im*c.re  ≡  b.re*c.im + b.im*c.re
        F::axiom_mul_congruence_left(a.re, b.re, c.im);
        F::axiom_mul_congruence_left(a.im, b.im, c.re);
        additive_group_lemmas::lemma_add_congruence::<F>(
            a.re.mul(c.im), b.re.mul(c.im),
            a.im.mul(c.re), b.im.mul(c.re),
        );
    }
}

} // verus!
