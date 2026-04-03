///  Dynamic tower spec type for arbitrary-depth quadratic extensions.
///
///  `DynTowerSpec<T>` is a concrete recursive spec type parameterized by a base
///  ordered field T. All operations are fully defined via structural recursion,
///  with Rat branches delegating to T's OrderedField axioms.
///
///  Proved trait impls: Equivalence, AdditiveCommutativeMonoid, AdditiveGroup.
///  Ring/Field/OrderedField impls were removed (contained assume(false) when
///  hardcoded to Rational). With generic T, these can be re-added once the
///  WellFormedDTS<W> wrapper is implemented (handles same_radicand preconditions).
use vstd::prelude::*;
use verus_algebra::traits::*;

verus! {

//  ═══════════════════════════════════════════════════════════════════
//   DynTowerSpec<T> — concrete recursive spec type for any tower depth
//  ═══════════════════════════════════════════════════════════════════

///  Concrete spec-level element of the quadratic extension tower over base field T.
///
///  - `Rat(t)`: base-level element in T
///  - `Ext(re, im, d)`: element `re + im·√d` where re, im, d are at one level lower.
pub ghost enum DynTowerSpec<T: OrderedField> {
    Rat(T),
    Ext(Box<DynTowerSpec<T>>, Box<DynTowerSpec<T>>, Box<DynTowerSpec<T>>),
}


//  ═══════════════════════════════════════════════════════════════════
//   Helper spec functions
//  ═══════════════════════════════════════════════════════════════════

///  Tower depth: Rat = 0, Ext = 1 + max depth of components.
pub open spec fn dts_depth<T: OrderedField>(x: DynTowerSpec<T>) -> nat
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

///  Check if a DynTowerSpec value is zero at all levels.
pub open spec fn dts_is_zero<T: OrderedField>(x: DynTowerSpec<T>) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => r.eqv(T::zero()),
        DynTowerSpec::Ext(re, im, _) => dts_is_zero(*re) && dts_is_zero(*im),
    }
}

//  ═══════════════════════════════════════════════════════════════════
//   Equivalence
//  ═══════════════════════════════════════════════════════════════════

///  Component-wise equivalence (ignoring radicand d).
///  Cross-depth: Rat(r) ≡ Ext(re, im, d) iff re ≡ Rat(r) and im is zero.
pub open spec fn dts_eqv<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> bool
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

///  Two DynTowerSpec values have the same radicand structure.
pub open spec fn dts_same_radicand<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> bool
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => true,
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, d2)) =>
            *d1 == *d2 && dts_same_radicand(*re1, *re2) && dts_same_radicand(*im1, *im2),
        _ => false,
    }
}

//  ═══════════════════════════════════════════════════════════════════
//   Constants
//  ═══════════════════════════════════════════════════════════════════

pub open spec fn dts_zero<T: OrderedField>() -> DynTowerSpec<T> {
    DynTowerSpec::Rat(T::zero())
}

pub open spec fn dts_one<T: OrderedField>() -> DynTowerSpec<T> {
    DynTowerSpec::Rat(T::one())
}

//  ═══════════════════════════════════════════════════════════════════
//   Additive operations
//  ═══════════════════════════════════════════════════════════════════

///  Negation: component-wise.
pub open spec fn dts_neg<T: OrderedField>(a: DynTowerSpec<T>) -> DynTowerSpec<T>
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.neg()),
        DynTowerSpec::Ext(re, im, d) => DynTowerSpec::Ext(
            Box::new(dts_neg(*re)),
            Box::new(dts_neg(*im)),
            d,
        ),
    }
}

///  Addition. Cross-depth: Rat + Ext adds to the real component only.
pub open spec fn dts_add<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> DynTowerSpec<T>
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) =>
            DynTowerSpec::Rat(r1.add(r2)),
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

///  Subtraction: a - b = a + (-b).
pub open spec fn dts_sub<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> DynTowerSpec<T> {
    dts_add(a, dts_neg(b))
}

//  ═══════════════════════════════════════════════════════════════════
//   Multiplicative operations
//  ═══════════════════════════════════════════════════════════════════

///  Multiplication.
///  Ext-Ext: (a_re + a_im√d)(b_re + b_im√d) = (a_re·b_re + d·a_im·b_im) + (a_re·b_im + a_im·b_re)√d
///  Cross-depth: Rat(r) · Ext(re, im, d) = Ext(Rat(r)·re, Rat(r)·im, d)
///
///  Note: d·(im1·im2) is used instead of (im1·im2)·d to ensure the first
///  argument to each recursive dts_mul call is a structural sub-field of `a`,
///  guaranteeing termination via `decreases a, b`.
pub open spec fn dts_mul<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> DynTowerSpec<T>
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) =>
            DynTowerSpec::Rat(r1.mul(r2)),
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
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

///  Conjugate: a + b√d ↦ a - b√d
pub open spec fn dts_conj<T: OrderedField>(a: DynTowerSpec<T>) -> DynTowerSpec<T>
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

///  Norm: (a + b√d)(a - b√d) = a² - d·b²
///  Returns a value at depth k-1 for a depth-k element.
pub open spec fn dts_norm<T: OrderedField>(a: DynTowerSpec<T>) -> DynTowerSpec<T>
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.mul(r)),
        DynTowerSpec::Ext(re, im, d) => {
            let re2 = dts_mul(*re, *re);
            let im2 = dts_mul(*im, *im);
            let d_im2 = dts_mul(*d, im2);
            dts_sub(re2, d_im2)
        },
    }
}

///  Reciprocal with explicit fuel for termination.
///  fuel should be >= dts_depth(a).
pub open spec fn dts_recip_fuel<T: OrderedField>(a: DynTowerSpec<T>, fuel: nat) -> DynTowerSpec<T>
    decreases fuel,
{
    match a {
        DynTowerSpec::Rat(r) => DynTowerSpec::Rat(r.recip()),
        DynTowerSpec::Ext(re, im, d) => {
            if fuel == 0 {
                a //  sentinel: insufficient fuel
            } else {
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

///  Reciprocal: 1/a with canonical fuel = depth + 1.
pub open spec fn dts_recip<T: OrderedField>(a: DynTowerSpec<T>) -> DynTowerSpec<T> {
    dts_recip_fuel(a, dts_depth(a) + 1)
}

///  Division: a / b = a · (1/b).
pub open spec fn dts_div<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> DynTowerSpec<T> {
    dts_mul(a, dts_recip(b))
}

//  ═══════════════════════════════════════════════════════════════════
//   Ordering
//  ═══════════════════════════════════════════════════════════════════

///  Non-negativity with explicit fuel.
pub open spec fn dts_nonneg_fuel<T: OrderedField>(x: DynTowerSpec<T>, fuel: nat) -> bool
    decreases fuel,
{
    match x {
        DynTowerSpec::Rat(r) => T::zero().le(r),
        DynTowerSpec::Ext(re, im, d) => {
            if fuel == 0 {
                false
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

///  Non-negativity with canonical fuel.
pub open spec fn dts_nonneg<T: OrderedField>(x: DynTowerSpec<T>) -> bool {
    dts_nonneg_fuel(x, dts_depth(x) + 1)
}

///  Less-than-or-equal: a <= b iff b - a >= 0.
pub open spec fn dts_le<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> bool {
    dts_nonneg(dts_sub(b, a))
}

///  Strict less-than: a < b iff a <= b and a ≢ b.
pub open spec fn dts_lt<T: OrderedField>(a: DynTowerSpec<T>, b: DynTowerSpec<T>) -> bool {
    dts_le(a, b) && !dts_eqv(a, b)
}

//  ═══════════════════════════════════════════════════════════════════
//   Well-formedness predicates
//  ═══════════════════════════════════════════════════════════════════

///  A DynTowerSpec value is well-formed when all sub-components at each
///  depth level have the same radicand structure.
pub open spec fn dts_well_formed<T: OrderedField>(x: DynTowerSpec<T>) -> bool
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

///  All radicands in the tower are non-negative.
pub open spec fn dts_nonneg_radicands<T: OrderedField>(x: DynTowerSpec<T>) -> bool
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

///  Non-degenerate tower: every radicand is not a "square" at that level.
pub open spec fn dts_nonsquare_radicands<T: OrderedField>(x: DynTowerSpec<T>) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_nonsquare_radicands(*re)
            && dts_nonsquare_radicands(*im)
            && dts_nonsquare_radicands(*d)
            && !dts_is_base_square(*d),
    }
}

///  A DTS value is a base-field perfect square if it's Rat(r) where r = s² for some s in T.
pub open spec fn dts_is_base_square<T: OrderedField>(d: DynTowerSpec<T>) -> bool {
    match d {
        DynTowerSpec::Rat(r) => exists|s: T| s.mul(s).eqv(r),
        DynTowerSpec::Ext(..) => false,
    }
}

///  Norm-definiteness: at every Ext level, for ANY values a,b with the same
///  radicand d, if norm (a²-d*b²) is structurally zero then both a and b are
///  structurally zero.
pub open spec fn dts_norm_definite<T: OrderedField>(x: DynTowerSpec<T>) -> bool
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => true,
        DynTowerSpec::Ext(re, im, d) =>
            dts_norm_definite(*re)
            && dts_norm_definite(*im)
            && dts_norm_definite(*d)
            && (forall|a2: DynTowerSpec<T>, b2: DynTowerSpec<T>|
                dts_is_zero(#[trigger] dts_sub(dts_mul(a2, a2), dts_mul(*d, dts_mul(b2, b2))))
                ==> (dts_is_zero(a2) && dts_is_zero(b2))),
    }
}

} //  verus!
