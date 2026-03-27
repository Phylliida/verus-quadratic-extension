/// Dynamic tower spec type for arbitrary-depth quadratic extensions.
///
/// `DynTowerSpec` is a concrete recursive spec type that mirrors `DynFieldElem`
/// at the specification level. All operations are fully defined, enabling
/// proofs by structural induction.
///
/// Proved trait impls: Equivalence, AdditiveCommutativeMonoid, AdditiveGroup.
/// Ring/Field/OrderedField impls were removed (contained assume(false)).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_rational::rational::Rational;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  DynTowerSpec — concrete recursive spec type for any tower depth
// ═══════════════════════════════════════════════════════════════════

/// Concrete spec-level element of the quadratic extension tower.
///
/// - `Rat(r)`: base-level rational element in Q
/// - `Ext(re, im, d)`: element `re + im·√d` where re, im, d are at one level lower.
///
/// Unlike the old abstract `DynTowerField`, all operations are concretely defined,
/// enabling the OrderedField axioms to be proved by structural induction.
pub ghost enum DynTowerSpec {
    Rat(Rational),
    Ext(Box<DynTowerSpec>, Box<DynTowerSpec>, Box<DynTowerSpec>),
}


// ═══════════════════════════════════════════════════════════════════
//  Helper spec functions
// ═══════════════════════════════════════════════════════════════════

/// Tower depth: Rat = 0, Ext = 1 + max depth of components.
pub open spec fn dts_depth(x: DynTowerSpec) -> nat
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => 0,
        DynTowerSpec::Ext(re, im, d) => {
            let dr = dts_depth(*re);
            let di = dts_depth(*im);
            let dd = dts_depth(*d);
            let m = if dr >= di { if dr >= dd { dr } else { dd } }
                    else { if di >= dd { di } else { dd } };
            1 + m
        },
    }
}

/// Check if a DynTowerSpec value is zero at all levels.
pub open spec fn dts_is_zero(x: DynTowerSpec) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => r.eqv(Rational::from_int_spec(0)),
        DynTowerSpec::Ext(re, im, _) => dts_is_zero(*re) && dts_is_zero(*im),
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Equivalence
// ═══════════════════════════════════════════════════════════════════

/// Component-wise equivalence (ignoring radicand d).
/// Cross-depth: Rat(r) ≡ Ext(re, im, d) iff re ≡ Rat(r) and im is zero.
pub open spec fn dts_eqv(a: DynTowerSpec, b: DynTowerSpec) -> bool
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => r1.eqv(r2),
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) =>
            dts_eqv(*re1, *re2) && dts_eqv(*im1, *im2),
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) =>
            dts_eqv(DynTowerSpec::Rat(r), *re) && dts_is_zero(*im),
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) =>
            dts_eqv(*re, DynTowerSpec::Rat(r)) && dts_is_zero(*im),
    }
}

/// Two DynTowerSpec values have the same radicand structure:
/// both Rat, or both Ext with structurally equal radicands AND
/// recursively same-radicand re and im components.
/// Required for mul_congruence (dts_mul uses the radicand from its arguments,
/// but dts_eqv ignores radicands).
///
/// NOTE: mul_congruence_right using this predicate is partially proved
/// but requires additional lemmas (mul preserves same_radicand, same_radicand
/// holds for all dts_model outputs from the same tower). The existential
/// witness approach in constraint_satisfied_dts is fully verified and avoids
/// needing these lemmas.
pub open spec fn dts_same_radicand(a: DynTowerSpec, b: DynTowerSpec) -> bool
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => true,
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, d2)) =>
            *d1 == *d2 && dts_same_radicand(*re1, *re2) && dts_same_radicand(*im1, *im2),
        _ => false, // cross-depth: incompatible structure for mul congruence
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Constants
// ═══════════════════════════════════════════════════════════════════

pub open spec fn dts_zero() -> DynTowerSpec {
    DynTowerSpec::Rat(Rational::from_int_spec(0))
}

pub open spec fn dts_one() -> DynTowerSpec {
    DynTowerSpec::Rat(Rational::from_int_spec(1))
}

// ═══════════════════════════════════════════════════════════════════
//  Additive operations
// ═══════════════════════════════════════════════════════════════════

/// Negation: component-wise.
pub open spec fn dts_neg(a: DynTowerSpec) -> DynTowerSpec
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.neg_spec()),
        DynTowerSpec::Ext(re, im, d) => DynTowerSpec::Ext(
            Box::new(dts_neg(*re)),
            Box::new(dts_neg(*im)),
            d,
        ),
    }
}

/// Addition. Cross-depth: Rat + Ext adds to the real component only.
pub open spec fn dts_add(a: DynTowerSpec, b: DynTowerSpec) -> DynTowerSpec
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) =>
            DynTowerSpec::Rat(r1.add_spec(r2)),
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) =>
            DynTowerSpec::Ext(
                Box::new(dts_add(*re1, *re2)),
                Box::new(dts_add(*im1, *im2)),
                d,
            ),
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) =>
            DynTowerSpec::Ext(
                Box::new(dts_add(DynTowerSpec::Rat(r), *re)),
                im,
                d,
            ),
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) =>
            DynTowerSpec::Ext(
                Box::new(dts_add(*re, DynTowerSpec::Rat(r))),
                im,
                d,
            ),
    }
}

/// Subtraction: a - b = a + (-b).
pub open spec fn dts_sub(a: DynTowerSpec, b: DynTowerSpec) -> DynTowerSpec {
    dts_add(a, dts_neg(b))
}

// ═══════════════════════════════════════════════════════════════════
//  Multiplicative operations
// ═══════════════════════════════════════════════════════════════════

/// Multiplication.
/// Ext-Ext: (a_re + a_im√d)(b_re + b_im√d) = (a_re·b_re + d·a_im·b_im) + (a_re·b_im + a_im·b_re)√d
/// Cross-depth: Rat(r) · Ext(re, im, d) = Ext(Rat(r)·re, Rat(r)·im, d)
///
/// Note: d·(im1·im2) is used instead of (im1·im2)·d to ensure the first
/// argument to each recursive dts_mul call is a structural sub-field of `a`,
/// guaranteeing termination via `decreases a, b`.
pub open spec fn dts_mul(a: DynTowerSpec, b: DynTowerSpec) -> DynTowerSpec
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) =>
            DynTowerSpec::Rat(r1.mul_spec(r2)),
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            // (re1 + im1·√d)(re2 + im2·√d) = (re1·re2 + d·im1·im2) + (re1·im2 + im1·re2)·√d
            let re1_re2 = dts_mul(*re1, *re2);
            let im1_im2 = dts_mul(*im1, *im2);
            let d_im1im2 = dts_mul(*d, im1_im2);
            let re1_im2 = dts_mul(*re1, *im2);
            let im1_re2 = dts_mul(*im1, *re2);
            DynTowerSpec::Ext(
                Box::new(dts_add(re1_re2, d_im1im2)),
                Box::new(dts_add(re1_im2, im1_re2)),
                d,
            )
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) =>
            DynTowerSpec::Ext(
                Box::new(dts_mul(DynTowerSpec::Rat(r), *re)),
                Box::new(dts_mul(DynTowerSpec::Rat(r), *im)),
                d,
            ),
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) =>
            DynTowerSpec::Ext(
                Box::new(dts_mul(*re, DynTowerSpec::Rat(r))),
                Box::new(dts_mul(*im, DynTowerSpec::Rat(r))),
                d,
            ),
    }
}

/// Conjugate: a + b√d ↦ a - b√d
pub open spec fn dts_conj(a: DynTowerSpec) -> DynTowerSpec
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r),
        DynTowerSpec::Ext(re, im, d) => DynTowerSpec::Ext(
            re,
            Box::new(dts_neg(*im)),
            d,
        ),
    }
}

/// Norm: (a + b√d)(a - b√d) = a² - d·b²
/// Returns a value at depth k-1 for a depth-k element.
pub open spec fn dts_norm(a: DynTowerSpec) -> DynTowerSpec
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.mul_spec(r)),
        DynTowerSpec::Ext(re, im, d) => {
            let re2 = dts_mul(*re, *re);
            let im2 = dts_mul(*im, *im);
            let d_im2 = dts_mul(*d, im2);
            dts_sub(re2, d_im2)
        },
    }
}

/// Reciprocal with explicit fuel for termination.
/// fuel should be >= dts_depth(a).
pub open spec fn dts_recip_fuel(a: DynTowerSpec, fuel: nat) -> DynTowerSpec
    decreases fuel,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.reciprocal_spec()),
        DynTowerSpec::Ext(re, im, d) => {
            if fuel == 0 {
                a // sentinel: insufficient fuel
            } else {
                // 1/(re + im·√d) = (re - im·√d) / (re² - d·im²)
                // = re/norm + (-im/norm)·√d  where norm = re² - d·im²
                let norm = dts_norm(a);
                let norm_inv = dts_recip_fuel(norm, (fuel - 1) as nat);
                DynTowerSpec::Ext(
                    Box::new(dts_mul(*re, norm_inv)),
                    Box::new(dts_neg(dts_mul(*im, norm_inv))),
                    d,
                )
            }
        },
    }
}

/// Reciprocal: 1/a with canonical fuel = depth + 1.
pub open spec fn dts_recip(a: DynTowerSpec) -> DynTowerSpec {
    dts_recip_fuel(a, dts_depth(a) + 1)
}

/// Division: a / b = a · (1/b).
pub open spec fn dts_div(a: DynTowerSpec, b: DynTowerSpec) -> DynTowerSpec {
    dts_mul(a, dts_recip(b))
}

// ═══════════════════════════════════════════════════════════════════
//  Ordering
// ═══════════════════════════════════════════════════════════════════

/// Non-negativity with explicit fuel.
/// Mirrors qe_nonneg: x = re + im·√d is nonneg iff:
///   (re >= 0 && im >= 0) ||
///   (re >= 0 && im < 0 && d·im² <= re²) ||
///   (re < 0 && im > 0 && re² <= d·im²)
pub open spec fn dts_nonneg_fuel(x: DynTowerSpec, fuel: nat) -> bool
    decreases fuel,
{
    match x {
        DynTowerSpec::Rat(r) => Rational::from_int_spec(0).le_spec(r),
        DynTowerSpec::Ext(re, im, d) => {
            if fuel == 0 {
                false // sentinel: insufficient fuel
            } else {
                let f = (fuel - 1) as nat;
                let a = *re;
                let b = *im;
                let a2 = dts_mul(a, a);
                let b2 = dts_mul(b, b);
                let b2d = dts_mul(*d, b2);
                let a_nn = dts_nonneg_fuel(a, f);
                let b_nn = dts_nonneg_fuel(b, f);
                let a_neg = dts_nonneg_fuel(dts_neg(a), f) && !dts_is_zero(a);
                let b_neg = dts_nonneg_fuel(dts_neg(b), f) && !dts_is_zero(b);
                let b_pos = b_nn && !dts_is_zero(b);
                let b2d_le_a2 = dts_nonneg_fuel(dts_sub(a2, b2d), f);
                let a2_le_b2d = dts_nonneg_fuel(dts_sub(b2d, a2), f);
                (a_nn && b_nn)
                || (a_nn && b_neg && b2d_le_a2)
                || (a_neg && b_pos && a2_le_b2d)
            }
        },
    }
}

/// Non-negativity with canonical fuel.
pub open spec fn dts_nonneg(x: DynTowerSpec) -> bool {
    dts_nonneg_fuel(x, dts_depth(x) + 1)
}

/// Less-than-or-equal: a <= b iff b - a >= 0.
pub open spec fn dts_le(a: DynTowerSpec, b: DynTowerSpec) -> bool {
    dts_nonneg(dts_sub(b, a))
}

/// Strict less-than: a < b iff a <= b and a ≢ b.
pub open spec fn dts_lt(a: DynTowerSpec, b: DynTowerSpec) -> bool {
    dts_le(a, b) && !dts_eqv(a, b)
}

// ═══════════════════════════════════════════════════════════════════
//  Trait implementations
// ═══════════════════════════════════════════════════════════════════

impl Equivalence for DynTowerSpec {
    open spec fn eqv(self, other: Self) -> bool {
        dts_eqv(self, other)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        crate::dyn_tower_lemmas::lemma_dts_eqv_reflexive(a);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        crate::dyn_tower_lemmas::lemma_dts_eqv_symmetric(a, b);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        crate::dyn_tower_lemmas::lemma_dts_eqv_transitive(a, b, c);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        crate::dyn_tower_lemmas::lemma_dts_eq_implies_eqv(a, b);
    }
}

impl AdditiveCommutativeMonoid for DynTowerSpec {
    open spec fn zero() -> Self {
        dts_zero()
    }

    open spec fn add(self, other: Self) -> Self {
        dts_add(self, other)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        crate::dyn_tower_lemmas::lemma_dts_add_commutative(a, b);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        crate::dyn_tower_lemmas::lemma_dts_add_associative(a, b, c);
    }

    proof fn axiom_add_zero_right(a: Self) {
        crate::dyn_tower_lemmas::lemma_dts_add_zero_right(a);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        crate::dyn_tower_lemmas::lemma_dts_add_congruence_left(a, b, c);
    }
}

impl AdditiveGroup for DynTowerSpec {
    open spec fn neg(self) -> Self {
        dts_neg(self)
    }

    open spec fn sub(self, other: Self) -> Self {
        dts_sub(self, other)
    }

    proof fn axiom_add_inverse_right(a: Self) {
        crate::dyn_tower_lemmas::lemma_dts_add_inverse_right(a);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        crate::dyn_tower_lemmas::lemma_dts_sub_is_add_neg(a, b);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        crate::dyn_tower_lemmas::lemma_dts_neg_congruence(a, b);
    }
}

// Ring/Field/PartialOrder/OrderedRing/OrderedField impls for DynTowerSpec
// were removed: they contained 12 assume(false) for hard structural induction
// proofs (mul_commutative, mul_associative, mul_distributes_left,
// mul_congruence_left, mul_recip_right, recip_congruence, le_antisymmetric,
// le_transitive, le_congruence, le_total, le_add_monotone,
// le_mul_nonneg_monotone). The DynFieldElem pipeline bypasses these traits
// entirely, using dyn_* methods directly.
//
// DynTowerRadicand was also removed: it used arbitrary() for value() and
// assume(false) for non_square/positive axioms. The pipeline stores radicands
// dynamically in each DynFieldElem::Extension node.

/// A DynTowerSpec value is well-formed when all sub-components at each
/// depth level have the same radicand structure. This holds for all values
/// constructed by the dyn solver (built from a single quadratic tower).
///
/// Formally: for Ext(re, im, d), both re and im must be well-formed,
/// AND same_radicand(re, im) (they share the same radicand structure).
pub open spec fn dts_well_formed(x: DynTowerSpec) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_well_formed(*re)
            && dts_well_formed(*im)
            && dts_well_formed(*d)
            && dts_same_radicand(*re, *im)
            && dts_same_radicand(*re, *d),
    }
}

/// All radicands in the tower are non-negative.
/// Required for ordered field properties (square_nonneg, nonneg_mul, etc.)
/// since Q(√d) with d < 0 gives a complex (unordered) extension.
/// In the constraint solver, all radicands come from discriminants A·r² - h²,
/// which are nonneg when the circle-line intersection exists.
pub open spec fn dts_nonneg_radicands(x: DynTowerSpec) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_nonneg_radicands(*re)
            && dts_nonneg_radicands(*im)
            && dts_nonneg_radicands(*d)
            && dts_nonneg(*d),
    }
}

/// Non-degenerate tower: every radicand is not a rational perfect square.
/// This ensures le_antisymmetric holds: nonneg(x) ∧ nonneg(neg(x)) → is_zero(x).
/// The solver always satisfies this (circle discriminants are never perfect squares).
pub open spec fn dts_nonsquare_radicands(x: DynTowerSpec) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_nonsquare_radicands(*re)
            && dts_nonsquare_radicands(*im)
            && dts_nonsquare_radicands(*d)
            && !dts_is_rational_square(*d),
    }
}

/// A DTS value is a rational perfect square if it's Rat(r) where r = s² for some rational s.
pub open spec fn dts_is_rational_square(d: DynTowerSpec) -> bool {
    match d {
        DynTowerSpec::Rat(r) => exists|s: Rational| s.mul_spec(s).eqv_spec(r),
        DynTowerSpec::Ext(..) => false,
    }
}

/// Norm-definiteness: at every Ext level, for ANY values a,b with the same
/// radicand d, if norm (a²-d*b²) is structurally zero then both a and b are
/// structurally zero. This captures "d is non-square in the field generated
/// by lower levels" and automatically propagates to computed values (products,
/// sums, norms) since they share the same radicand.
///
/// For depth-1 towers (Rat radicands), this follows from dts_nonsquare_radicands.
/// The solver establishes this for its specific radicands.
pub open spec fn dts_norm_definite(x: DynTowerSpec) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_norm_definite(*re)
            && dts_norm_definite(*im)
            && dts_norm_definite(*d)
            && (forall|a2: DynTowerSpec, b2: DynTowerSpec|
                dts_is_zero(#[trigger] dts_sub(dts_mul(a2, a2), dts_mul(*d, dts_mul(b2, b2))))
                ==> (dts_is_zero(a2) && dts_is_zero(b2))),
    }
}

} // verus!
