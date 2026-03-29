use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::field::Field;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use crate::radicand::Radicand;
use crate::spec::*;
use crate::lemmas;

verus! {

impl<F: Field, R: Radicand<F>> Field for SpecQuadExt<F, R> {
    open spec fn recip(self) -> Self {
        qe_recip::<F, R>(self)
    }

    open spec fn div(self, other: Self) -> Self {
        qe_div::<F, R>(self, other)
    }

    //  ── Multiplicative inverse: x * recip(x) ≡ 1 ───────────────────
    //
    //  (a + b√d) · (a·n⁻¹ + (-b)·n⁻¹·√d)
    //    where n = a² - b²d
    //
    //  Real part: a·(a·n⁻¹) + b·((-b)·n⁻¹)·d
    //           = a²·n⁻¹ - b²·d·n⁻¹
    //           = (a² - b²d)·n⁻¹
    //           = n·n⁻¹ = 1
    //
    //  Imaginary part: a·((-b)·n⁻¹) + b·(a·n⁻¹)
    //                = -a·b·n⁻¹ + b·a·n⁻¹
    //                = 0

    #[verifier::rlimit(30)]
    proof fn axiom_mul_recip_right(x: Self) {
        //  First establish that the norm is nonzero
        lemmas::lemma_norm_nonzero::<F, R>(x);
        lemmas::lemma_mul_recip_right_re::<F, R>(x);
        lemmas::lemma_mul_recip_right_im::<F, R>(x);
    }

    ///  div(a, b) ≡ mul(a, recip(b))
    proof fn axiom_div_is_mul_recip(a: Self, b: Self) {
        //  qe_div is defined as qe_mul(a, qe_recip(b)), which matches
        //  Self::mul(a, Self::recip(b)) by definition.
        F::axiom_eqv_reflexive(qe_div::<F, R>(a, b).re);
        F::axiom_eqv_reflexive(qe_div::<F, R>(a, b).im);
    }

    ///  recip respects equivalence
    proof fn axiom_recip_congruence(a: Self, b: Self) {
        //  a ≡ b means a.re ≡ b.re and a.im ≡ b.im
        //  Need: norm(a) ≡ norm(b), then recip components are congruent

        let d = R::value();

        //  norm(a) = a.re² - a.im²·d
        //  norm(b) = b.re² - b.im²·d
        //  a.re ≡ b.re → a.re² ≡ b.re²
        ring_lemmas::lemma_mul_congruence::<F>(a.re, b.re, a.re, b.re);
        //  a.im ≡ b.im → a.im² ≡ b.im²
        ring_lemmas::lemma_mul_congruence::<F>(a.im, b.im, a.im, b.im);
        //  a.im²·d ≡ b.im²·d
        F::axiom_mul_congruence_left(a.im.mul(a.im), b.im.mul(b.im), d);
        //  norm(a) ≡ norm(b)
        additive_group_lemmas::lemma_sub_congruence::<F>(
            a.re.mul(a.re), b.re.mul(b.re),
            a.im.mul(a.im).mul(d), b.im.mul(b.im).mul(d),
        );

        let na = qe_norm::<F, R>(a);
        let nb = qe_norm::<F, R>(b);

        //  !a.eqv(zero) → norm(a) ≢ 0
        lemmas::lemma_norm_nonzero::<F, R>(a);

        //  norm(a) ≡ norm(b) and norm(a) ≢ 0 → recip(norm(a)) ≡ recip(norm(b))
        F::axiom_recip_congruence(na, nb);

        //  re: a.re·recip(na) ≡ b.re·recip(nb)
        ring_lemmas::lemma_mul_congruence::<F>(a.re, b.re, na.recip(), nb.recip());

        //  im: (-a.im)·recip(na) ≡ (-b.im)·recip(nb)
        F::axiom_neg_congruence(a.im, b.im);
        ring_lemmas::lemma_mul_congruence::<F>(a.im.neg(), b.im.neg(), na.recip(), nb.recip());
    }
}

} //  verus!
