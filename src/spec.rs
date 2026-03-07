use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::field::Field;
use crate::radicand::Radicand;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Spec type: elements of the quadratic extension F(√d)
// ═══════════════════════════════════════════════════════════════════

/// Spec-level element of the quadratic extension F(√d).
///
/// Represents re + im·√d where d = R::value().
/// The radicand is fixed at the type level via R, so it's not stored per-element.
/// This means SpecQuadExt<F, R1> and SpecQuadExt<F, R2> are distinct types
/// for distinct radicands, which is mathematically correct.
pub ghost struct SpecQuadExt<F, R> {
    pub re: F,
    pub im: F,
    pub _phantom: core::marker::PhantomData<R>,
}

/// Constructor that avoids writing PhantomData everywhere.
pub open spec fn qext<F, R>(re: F, im: F) -> SpecQuadExt<F, R> {
    SpecQuadExt { re, im, _phantom: core::marker::PhantomData }
}

// ═══════════════════════════════════════════════════════════════════
//  Open spec functions for quadratic extension arithmetic
// ═══════════════════════════════════════════════════════════════════

// These are `open` so Z3 can unfold them. Inside these bodies,
// F's operations (add, mul, etc.) are opaque — Z3 only knows them
// through F's axioms. This is the key abstraction barrier.

/// Zero: 0 + 0·√d
pub open spec fn qe_zero<F: Field, R: Radicand<F>>() -> SpecQuadExt<F, R> {
    qext(F::zero(), F::zero())
}

/// One: 1 + 0·√d
pub open spec fn qe_one<F: Field, R: Radicand<F>>() -> SpecQuadExt<F, R> {
    qext(F::one(), F::zero())
}

/// Addition: (a + b√d) + (c + e√d) = (a+c) + (b+e)√d
pub open spec fn qe_add<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    qext(x.re.add(y.re), x.im.add(y.im))
}

/// Negation: -(a + b√d) = (-a) + (-b)√d
pub open spec fn qe_neg<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    qext(x.re.neg(), x.im.neg())
}

/// Subtraction: component-wise
pub open spec fn qe_sub<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    qext(x.re.sub(y.re), x.im.sub(y.im))
}

/// Multiplication: (a + b√d)(c + e√d) = (ac + bed) + (ae + bc)√d
pub open spec fn qe_mul<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    let d = R::value();
    qext(
        x.re.mul(y.re).add(x.im.mul(y.im).mul(d)),
        x.re.mul(y.im).add(x.im.mul(y.re)),
    )
}

/// Conjugate: a + b√d  ↦  a - b√d
pub open spec fn qe_conj<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    qext(x.re, x.im.neg())
}

/// Norm: (a + b√d)(a - b√d) = a² - b²d  (an element of F, not of the extension)
pub open spec fn qe_norm<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
) -> F {
    let d = R::value();
    x.re.mul(x.re).sub(x.im.mul(x.im).mul(d))
}

/// Multiplicative inverse: conjugate / norm
///
/// (a + b√d)⁻¹ = (a - b√d) / (a² - b²d)
///              = (a·n⁻¹) + (-b·n⁻¹)√d  where n = a² - b²d
pub open spec fn qe_recip<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    let n_inv = qe_norm::<F, R>(x).recip();
    qext(
        x.re.mul(n_inv),
        x.im.neg().mul(n_inv),
    )
}

/// Division: x * recip(y)
pub open spec fn qe_div<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> SpecQuadExt<F, R> {
    qe_mul::<F, R>(x, qe_recip::<F, R>(y))
}

/// Equivalence: component-wise in the base field.
pub open spec fn qe_eqv<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
) -> bool {
    x.re.eqv(y.re) && x.im.eqv(y.im)
}

} // verus!
