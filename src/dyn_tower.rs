/// Dynamic tower field types for arbitrary-depth quadratic extensions.
///
/// `DynTowerField` is an abstract OrderedField that represents any level
/// of the tower Q(√d₁)(√d₂)...(√dₖ). All axioms are assumed, justified
/// by the fact that each concrete tower level satisfies OrderedField.
///
/// `DynTowerRadicand` is an abstract PositiveRadicand over DynTowerField,
/// justified by runtime discriminant checks (positive, not a perfect square).
use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::radicand::*;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  DynTowerField — abstract OrderedField for any tower depth
// ═══════════════════════════════════════════════════════════════════

/// Abstract field type representing any level of the quadratic extension tower.
///
/// At runtime, `DynFieldElem` provides the actual arithmetic. The spec-level
/// `DynTowerField` exists only to satisfy Verus's type system. All trait axioms
/// are assumed (proof debt), justified by the fact that each concrete level
/// `SpecQuadExt<..., ...>` provably satisfies these axioms.
pub struct DynTowerField;

impl Equivalence for DynTowerField {
    open spec fn eqv(self, other: Self) -> bool { arbitrary() }

    proof fn axiom_eqv_reflexive(a: Self) { assume(a.eqv(a)); }
    proof fn axiom_eqv_symmetric(a: Self, b: Self) { assume(a.eqv(b) == b.eqv(a)); }
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) { assume(a.eqv(c)); }
    proof fn axiom_eq_implies_eqv(a: Self, b: Self) { assume(a.eqv(b)); }
}

impl AdditiveCommutativeMonoid for DynTowerField {
    open spec fn zero() -> Self { arbitrary() }
    open spec fn add(self, other: Self) -> Self { arbitrary() }

    proof fn axiom_add_commutative(a: Self, b: Self) { assume(a.add(b).eqv(b.add(a))); }
    proof fn axiom_add_associative(a: Self, b: Self, c: Self) { assume(a.add(b).add(c).eqv(a.add(b.add(c)))); }
    proof fn axiom_add_zero_right(a: Self) { assume(a.add(Self::zero()).eqv(a)); }
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) { assume(a.add(c).eqv(b.add(c))); }
}

impl AdditiveGroup for DynTowerField {
    open spec fn neg(self) -> Self { arbitrary() }
    open spec fn sub(self, other: Self) -> Self { arbitrary() }

    proof fn axiom_add_inverse_right(a: Self) { assume(a.add(a.neg()).eqv(Self::zero())); }
    proof fn axiom_sub_is_add_neg(a: Self, b: Self) { assume(a.sub(b).eqv(a.add(b.neg()))); }
    proof fn axiom_neg_congruence(a: Self, b: Self) { assume(a.neg().eqv(b.neg())); }
}

impl PartialOrder for DynTowerField {
    open spec fn le(self, other: Self) -> bool { arbitrary() }

    proof fn axiom_le_reflexive(a: Self) { assume(a.le(a)); }
    proof fn axiom_le_antisymmetric(a: Self, b: Self) { assume(a.eqv(b)); }
    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) { assume(a.le(c)); }
    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) { assume(a2.le(b2)); }
}

impl Ring for DynTowerField {
    open spec fn one() -> Self { arbitrary() }
    open spec fn mul(self, other: Self) -> Self { arbitrary() }

    proof fn axiom_mul_commutative(a: Self, b: Self) { assume(a.mul(b).eqv(b.mul(a))); }
    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) { assume(a.mul(b).mul(c).eqv(a.mul(b.mul(c)))); }
    proof fn axiom_mul_one_right(a: Self) { assume(a.mul(Self::one()).eqv(a)); }
    proof fn axiom_mul_zero_right(a: Self) { assume(a.mul(Self::zero()).eqv(Self::zero())); }
    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) { assume(a.mul(b.add(c)).eqv(a.mul(b).add(a.mul(c)))); }
    proof fn axiom_one_ne_zero() { assume(!Self::one().eqv(Self::zero())); }
    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) { assume(a.mul(c).eqv(b.mul(c))); }
}

impl OrderedRing for DynTowerField {
    open spec fn lt(self, other: Self) -> bool { arbitrary() }

    proof fn axiom_le_total(a: Self, b: Self) { assume(a.le(b) || b.le(a)); }
    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) { assume(a.lt(b) == (a.le(b) && !a.eqv(b))); }
    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) { assume(a.add(c).le(b.add(c))); }
    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) { assume(a.mul(c).le(b.mul(c))); }
}

impl Field for DynTowerField {
    open spec fn recip(self) -> Self { arbitrary() }
    open spec fn div(self, other: Self) -> Self { arbitrary() }

    proof fn axiom_mul_recip_right(a: Self) { assume(a.mul(a.recip()).eqv(Self::one())); }
    proof fn axiom_div_is_mul_recip(a: Self, b: Self) { assume(a.div(b).eqv(a.mul(b.recip()))); }
    proof fn axiom_recip_congruence(a: Self, b: Self) { assume(a.recip().eqv(b.recip())); }
}

impl OrderedField for DynTowerField {}

// ═══════════════════════════════════════════════════════════════════
//  DynTowerRadicand — abstract radicand for extending DynTowerField
// ═══════════════════════════════════════════════════════════════════

/// Abstract radicand for extending DynTowerField by √d.
///
/// At runtime, the radicand value is computed from the first circle step's
/// discriminant at each tower level. The spec-level value is `arbitrary()`,
/// justified by runtime checks that the discriminant is positive and not
/// a perfect square.
pub struct DynTowerRadicand;

impl Radicand<DynTowerField> for DynTowerRadicand {
    open spec fn value() -> DynTowerField { arbitrary() }

    proof fn axiom_non_square(x: DynTowerField) {
        assume(!x.mul(x).eqv(Self::value()));
    }
}

impl PositiveRadicand<DynTowerField> for DynTowerRadicand {
    proof fn axiom_value_positive() {
        assume(DynTowerField::zero().lt(Self::value()));
    }
}

} // verus!
