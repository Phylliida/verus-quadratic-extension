use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;

verus! {

///  A radicand d in field F that is non-square.
///
///  This is a type-level witness: each implementor fixes a specific element
///  of F and proves it has no square root in F. This enables QuadExt<F, R>
///  to be a field — the non-square property guarantees that the norm
///  a² - b²d is nonzero for any nonzero a + b√d.
///
///  For nesting (e.g. ℚ(√2)(√(√2))), R2 would implement
///  `Radicand<QuadExt<Rational, R1>>` where the value is √2
///  (the element (0, 1) in ℚ(√2)).
pub trait Radicand<F: Field>: Sized {
    ///  The specific element of F used as the radicand.
    spec fn value() -> F;

    ///  Proof that the radicand is non-square in F:
    ///  no element of F squares to this value.
    proof fn axiom_non_square(x: F)
        ensures
            !x.mul(x).eqv(Self::value()),
    ;
}

///  Convenience spec: d is non-square in F iff no element squares to it.
pub open spec fn is_non_square<F: Field>(d: F) -> bool {
    forall|x: F| !x.mul(x).eqv(d)
}

///  A positive radicand in an ordered field.
///
///  Extends `Radicand<F>` with the constraint that the radicand value is
///  strictly positive in F. This is needed for the ordering on SpecQuadExt:
///  the sign of a + b√d depends on d > 0 so that √d is a positive real root.
pub trait PositiveRadicand<F: OrderedField>: Radicand<F> {
    ///  The radicand is strictly positive: 0 < d.
    proof fn axiom_value_positive()
        ensures
            F::zero().lt(Self::value()),
    ;
}

} //  verus!
