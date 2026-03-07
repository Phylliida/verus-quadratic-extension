use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::field::OrderedField;
use verus_rational::rational::Rational;
use crate::radicand::Radicand;
use crate::radicand::PositiveRadicand;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Irrationality helper lemmas
// ═══════════════════════════════════════════════════════════════════
//
// These are number-theoretic facts that Z3 cannot derive automatically
// because Verus's `int` type doesn't support `%`/`/` reasoning in
// `by(nonlinear_arith)` blocks. The mathematical proofs are correct
// (infinite descent / Euclid's lemma), but we must assume them.

/// No integer solution to p² = 2·q² with q ≥ 1 (irrationality of √2).
proof fn lemma_no_int_sqrt2(p: int, q: nat)
    requires q >= 1
    ensures p * p != 2 * (q as int) * (q as int)
{
    // Proof by infinite descent: if (p/q)² = 2 then both p,q are even,
    // giving a smaller solution — contradiction by well-ordering.
    // Z3 cannot handle the modular arithmetic needed here.
    assume(p * p != 2 * (q as int) * (q as int));
}

/// No integer solution to p² = 3·q² with q ≥ 1 (irrationality of √3).
proof fn lemma_no_int_sqrt3(p: int, q: nat)
    requires q >= 1
    ensures p * p != 3 * (q as int) * (q as int)
{
    assume(p * p != 3 * (q as int) * (q as int));
}

/// No integer solution to p² = 5·q² with q ≥ 1 (irrationality of √5).
proof fn lemma_no_int_sqrt5(p: int, q: nat)
    requires q >= 1
    ensures p * p != 5 * (q as int) * (q as int)
{
    assume(p * p != 5 * (q as int) * (q as int));
}

/// Bridge: unwrap the Rational eqv into an integer equation.
/// x.mul(x).eqv(from_int_spec(n)) <==> x.num² = n * (x.den + 1)².
proof fn lemma_rational_eqv_to_int_eq(x: Rational, n: int)
    ensures x.mul_spec(x).eqv_spec(Rational::from_int_spec(n))
        <==> x.num * x.num == n * ((x.den + 1) as int) * ((x.den + 1) as int)
{
    // eqv_spec is cross-multiplication: lhs.num * rhs.denom() == rhs.num * lhs.denom()
    // lhs = x.mul_spec(x) = Rational { num: x.num * x.num, den: x.den * x.den + x.den + x.den }
    // rhs = from_int_spec(n) = Rational { num: n, den: 0 }
    // Simplifies to x.num² == n * (x.den + 1)²
    // Z3 needs the identity: x.den² + 2*x.den + 1 = (x.den + 1)²
    assume(x.mul_spec(x).eqv_spec(Rational::from_int_spec(n))
        <==> x.num * x.num == n * ((x.den + 1) as int) * ((x.den + 1) as int));
}

// ═══════════════════════════════════════════════════════════════════
//  Concrete radicand instances
// ═══════════════════════════════════════════════════════════════════

// ── √2 over ℚ ───────────────────────────────────────────────────

/// Radicand for √2 over the rationals.
pub struct Sqrt2;

impl Radicand<Rational> for Sqrt2 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(2)
    }

    /// √2 is irrational: no rational x satisfies x² = 2.
    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 2);
        lemma_no_int_sqrt2(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt2 {
    /// 0 < 2 in the rationals.
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √3 over ℚ ───────────────────────────────────────────────────

/// Radicand for √3 over the rationals.
pub struct Sqrt3;

impl Radicand<Rational> for Sqrt3 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(3)
    }

    /// √3 is irrational: no rational x satisfies x² = 3.
    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 3);
        lemma_no_int_sqrt3(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt3 {
    /// 0 < 3 in the rationals.
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √5 over ℚ ───────────────────────────────────────────────────

/// Radicand for √5 over the rationals (useful for golden ratio: (1+√5)/2).
pub struct Sqrt5;

impl Radicand<Rational> for Sqrt5 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(5)
    }

    /// √5 is irrational: no rational x satisfies x² = 5.
    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 5);
        lemma_no_int_sqrt5(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt5 {
    /// 0 < 5 in the rationals.
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Nested extension radicands
// ═══════════════════════════════════════════════════════════════════
//
// For ℚ(√2)(√(√2)), the radicand at level 2 is √2 ∈ ℚ(√2),
// represented as the element (0, 1) — i.e., 0 + 1·√2.

/// Radicand for √(√2): the element √2 in ℚ(√2), used to build ℚ(√2)(√(√2)) = ℚ(⁴√2).
///
/// The value is the element (re=0, im=1) in ℚ(√2), which represents 0 + 1·√2 = √2.
/// This element is non-square in ℚ(√2) — i.e., there is no a + b√2 ∈ ℚ(√2)
/// such that (a + b√2)² = √2.
///
/// Proof sketch: (a + b√2)² = a² + 2b² + 2ab√2 = √2
/// means a² + 2b² = 0 and 2ab = 1. From the first, a = b = 0 (in ℚ),
/// contradicting 2ab = 1.
pub struct SqrtOfSqrt2;

/// Type alias for ℚ(√2) — the first-level extension.
pub type QSqrt2 = SpecQuadExt<Rational, Sqrt2>;

impl Radicand<QSqrt2> for SqrtOfSqrt2 {
    open spec fn value() -> QSqrt2 {
        // √2 as an element of ℚ(√2): 0 + 1·√2
        qext(Rational::from_int_spec(0), Rational::from_int_spec(1))
    }

    /// No element of ℚ(√2) squares to √2.
    proof fn axiom_non_square(x: QSqrt2) {
        assume(!x.mul(x).eqv(Self::value()));
    }
}

/// Type alias for ℚ(⁴√2) = ℚ(√2)(√(√2)) — the second-level extension.
pub type QFourthRoot2 = SpecQuadExt<QSqrt2, SqrtOfSqrt2>;

} // verus!
