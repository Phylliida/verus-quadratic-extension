use crate::radicand::Radicand;
use crate::spec::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::field::Field;
use vstd::prelude::*;

verus! {

impl<F: Field, R: Radicand<F>> Equivalence for SpecQuadExt<F, R> {
    /// Component-wise equivalence using the base field's eqv.
    open spec fn eqv(self, other: Self) -> bool {
        qe_eqv::<F, R>(self, other)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        F::axiom_eqv_reflexive(a.re);
        F::axiom_eqv_reflexive(a.im);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        F::axiom_eqv_symmetric(a.re, b.re);
        F::axiom_eqv_symmetric(a.im, b.im);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        F::axiom_eqv_transitive(a.re, b.re, c.re);
        F::axiom_eqv_transitive(a.im, b.im, c.im);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        if a == b {
            F::axiom_eq_implies_eqv(a.re, b.re);
            F::axiom_eq_implies_eqv(a.im, b.im);
        }
    }
}

} // verus!
