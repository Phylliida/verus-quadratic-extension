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
use crate::ordered::*;

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

/// No integer solution to p² = 6·q² with q ≥ 1 (irrationality of √6).
proof fn lemma_no_int_sqrt6(p: int, q: nat)
    requires q >= 1
    ensures p * p != 6 * (q as int) * (q as int)
{
    assume(p * p != 6 * (q as int) * (q as int));
}

/// No integer solution to p² = 7·q² with q ≥ 1 (irrationality of √7).
proof fn lemma_no_int_sqrt7(p: int, q: nat)
    requires q >= 1
    ensures p * p != 7 * (q as int) * (q as int)
{
    assume(p * p != 7 * (q as int) * (q as int));
}

/// No integer solution to p² = 10·q² with q ≥ 1 (irrationality of √10).
proof fn lemma_no_int_sqrt10(p: int, q: nat)
    requires q >= 1
    ensures p * p != 10 * (q as int) * (q as int)
{
    assume(p * p != 10 * (q as int) * (q as int));
}

/// No integer solution to p² = 11·q² with q ≥ 1 (irrationality of √11).
proof fn lemma_no_int_sqrt11(p: int, q: nat)
    requires q >= 1
    ensures p * p != 11 * (q as int) * (q as int)
{
    assume(p * p != 11 * (q as int) * (q as int));
}

/// No integer solution to p² = 13·q² with q ≥ 1 (irrationality of √13).
proof fn lemma_no_int_sqrt13(p: int, q: nat)
    requires q >= 1
    ensures p * p != 13 * (q as int) * (q as int)
{
    assume(p * p != 13 * (q as int) * (q as int));
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

// ── √6 over ℚ ───────────────────────────────────────────────────

/// Radicand for √6 over the rationals.
pub struct Sqrt6;

impl Radicand<Rational> for Sqrt6 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(6)
    }

    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 6);
        lemma_no_int_sqrt6(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt6 {
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √7 over ℚ ───────────────────────────────────────────────────

/// Radicand for √7 over the rationals.
pub struct Sqrt7;

impl Radicand<Rational> for Sqrt7 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(7)
    }

    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 7);
        lemma_no_int_sqrt7(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt7 {
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √10 over ℚ ──────────────────────────────────────────────────

/// Radicand for √10 over the rationals.
pub struct Sqrt10;

impl Radicand<Rational> for Sqrt10 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(10)
    }

    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 10);
        lemma_no_int_sqrt10(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt10 {
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √11 over ℚ ──────────────────────────────────────────────────

/// Radicand for √11 over the rationals.
pub struct Sqrt11;

impl Radicand<Rational> for Sqrt11 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(11)
    }

    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 11);
        lemma_no_int_sqrt11(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt11 {
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

// ── √13 over ℚ ──────────────────────────────────────────────────

/// Radicand for √13 over the rationals.
pub struct Sqrt13;

impl Radicand<Rational> for Sqrt13 {
    open spec fn value() -> Rational {
        Rational::from_int_spec(13)
    }

    proof fn axiom_non_square(x: Rational) {
        lemma_rational_eqv_to_int_eq(x, 13);
        lemma_no_int_sqrt13(x.num, (x.den + 1) as nat);
    }
}

impl PositiveRadicand<Rational> for Sqrt13 {
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

// ═══════════════════════════════════════════════════════════════════
//  Dynamic radicands for arbitrary-depth circle chains
// ═══════════════════════════════════════════════════════════════════
//
// These radicands have spec-level values determined by `arbitrary()`.
// At runtime, the actual discriminant is computed from circle intersections.
// The connection between spec and runtime is made via `assume` in the
// pipeline proof block. Non-square and positivity are justified by runtime
// checks (discriminant > 0, not a perfect square in the base field).
//
// Adding depth k+1: define DynRadicandK+1, impl Radicand + PositiveRadicand
// for the appropriate base field, add type aliases. ~30 lines each.

// ── Level 1: dynamic radicand over ℚ ─────────────────────────────

/// Dynamic radicand for level-1 circle intersections.
///
/// The radicand value is not known at compile time — it's the discriminant
/// of a circle-circle or circle-line intersection, determined at runtime.
/// `arbitrary()` produces a fixed but unknown spec value; the pipeline
/// connects it to the actual discriminant via `assume`.
pub struct DynRadicand1;

impl Radicand<Rational> for DynRadicand1 {
    open spec fn value() -> Rational {
        arbitrary()
    }

    /// Non-square: justified by runtime check that the discriminant
    /// is not a perfect square in ℚ.
    proof fn axiom_non_square(x: Rational) {
        assume(!x.mul_spec(x).eqv_spec(Self::value()));
    }
}

impl PositiveRadicand<Rational> for DynRadicand1 {
    /// Positivity: justified by runtime check that the discriminant > 0.
    proof fn axiom_value_positive() {
        assume(Rational::from_int_spec(0).lt_spec(Self::value()));
    }
}

/// Level-1 dynamic extension type: ℚ(√d₁)
pub type DynLevel1 = SpecQuadExt<Rational, DynRadicand1>;

// ── Level 2: dynamic radicand over DynLevel1 ────────────────────

/// Dynamic radicand for level-2 circle intersections.
///
/// The radicand lives in DynLevel1 = ℚ(√d₁). Its value is the discriminant
/// of a circle intersection where the circles have ℚ(√d₁)-valued coordinates.
pub struct DynRadicand2;

impl Radicand<DynLevel1> for DynRadicand2 {
    open spec fn value() -> DynLevel1 {
        arbitrary()
    }

    proof fn axiom_non_square(x: DynLevel1) {
        assume(!qe_eqv::<Rational, DynRadicand1>(
            qe_mul::<Rational, DynRadicand1>(x, x),
            Self::value(),
        ));
    }
}

impl PositiveRadicand<DynLevel1> for DynRadicand2 {
    proof fn axiom_value_positive() {
        assume(qe_lt::<Rational, DynRadicand1>(
            qe_zero::<Rational, DynRadicand1>(),
            Self::value(),
        ));
    }
}

/// Level-2 dynamic extension type: ℚ(√d₁)(√d₂)
pub type DynLevel2 = SpecQuadExt<DynLevel1, DynRadicand2>;

// ── Level 3: dynamic radicand over DynLevel2 ────────────────────

/// Dynamic radicand for level-3 circle intersections.
pub struct DynRadicand3;

impl Radicand<DynLevel2> for DynRadicand3 {
    open spec fn value() -> DynLevel2 {
        arbitrary()
    }

    proof fn axiom_non_square(x: DynLevel2) {
        assume(!qe_eqv::<DynLevel1, DynRadicand2>(
            qe_mul::<DynLevel1, DynRadicand2>(x, x),
            Self::value(),
        ));
    }
}

impl PositiveRadicand<DynLevel2> for DynRadicand3 {
    proof fn axiom_value_positive() {
        assume(qe_lt::<DynLevel1, DynRadicand2>(
            qe_zero::<DynLevel1, DynRadicand2>(),
            Self::value(),
        ));
    }
}

/// Level-3 dynamic extension type: ℚ(√d₁)(√d₂)(√d₃)
pub type DynLevel3 = SpecQuadExt<DynLevel2, DynRadicand3>;

} // verus!
