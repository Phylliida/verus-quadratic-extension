/// Axiom proof lemmas for DynTowerSpec.
///
/// Each lemma follows the pattern:
/// - Base case (Rat): delegate to Rational axiom
/// - Inductive case (Ext): recurse on components
/// - Cross-depth (Rat↔Ext): recurse into the Ext's re component
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_rational::rational::Rational;
use crate::dyn_tower::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Helper lemmas for is_zero / eqv interaction
// ═══════════════════════════════════════════════════════════════════

/// dts_eqv(x, Rat(0)) implies dts_is_zero(x).
pub proof fn lemma_dts_eqv_zero_implies_is_zero(x: DynTowerSpec)
    requires dts_eqv(x, dts_zero()),
    ensures dts_is_zero(x),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => {},
        DynTowerSpec::Ext(re, im, _) => {
            // eqv(Ext, Rat(0)) = eqv(*re, Rat(0)) && is_zero(*im)
            lemma_dts_eqv_zero_implies_is_zero(*re);
        },
    }
}

/// dts_is_zero(x) implies dts_eqv(x, Rat(0)).
pub proof fn lemma_dts_is_zero_implies_eqv_zero(x: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_eqv(x, dts_zero()),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => {},
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_is_zero_implies_eqv_zero(*re);
        },
    }
}

/// If is_zero(a) and eqv(a, b), then is_zero(b).
pub proof fn lemma_dts_is_zero_congruence(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_is_zero(a), dts_eqv(a, b),
    ensures dts_is_zero(b),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::axiom_eqv_symmetric(r1, r2);
            Rational::axiom_eqv_transitive(r2, r1, Rational::from_int_spec(0));
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_is_zero_congruence(*re1, *re2);
            lemma_dts_is_zero_congruence(*im1, *im2);
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) => {
            // is_zero(Rat(r)): r.eqv(0)
            // eqv = dts_eqv(Rat(r), *re) && is_zero(*im)
            // Need: is_zero(*re) — recurse
            lemma_dts_is_zero_congruence(DynTowerSpec::Rat(r), *re);
        },
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) => {
            // is_zero(Ext): is_zero(*re) && is_zero(*im)
            // eqv = dts_eqv(*re, Rat(r)) && is_zero(*im)
            // Need: is_zero(Rat(r)) — recurse
            lemma_dts_is_zero_congruence(*re, DynTowerSpec::Rat(r));
        },
    }
}

/// If both are zero, they're equivalent.
pub proof fn lemma_dts_is_zero_eqv(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_is_zero(a), dts_is_zero(b),
    ensures dts_eqv(a, b),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::axiom_eqv_symmetric(r2, Rational::from_int_spec(0));
            Rational::axiom_eqv_transitive(r1, Rational::from_int_spec(0), r2);
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_is_zero_eqv(*re1, *re2);
            lemma_dts_is_zero_eqv(*im1, *im2);
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) => {
            // Need: dts_eqv(Rat(r), *re) && is_zero(*im) — have is_zero(*im) ✓
            lemma_dts_is_zero_eqv(DynTowerSpec::Rat(r), *re);
        },
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) => {
            lemma_dts_is_zero_eqv(*re, DynTowerSpec::Rat(r));
        },
    }
}

/// If is_zero(x), then add(x, y) ≡ y. ("adding zero on the left")
pub proof fn lemma_dts_add_is_zero_left(x: DynTowerSpec, y: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_eqv(dts_add(x, y), y),
    decreases x, y,
{
    match (x, y) {
        (DynTowerSpec::Rat(r), DynTowerSpec::Rat(s)) => {
            // add(Rat(r), Rat(s)) = Rat(r+s). Need (r+s).eqv(s).
            // r.eqv(0) from is_zero. Use congruence + zero.
            Rational::axiom_add_congruence_left(r, Rational::from_int_spec(0), s);
            // Now: (r+s).eqv(0+s)
            Rational::axiom_add_commutative(Rational::from_int_spec(0), s);
            // (0+s).eqv(s+0)
            Rational::axiom_add_zero_right(s);
            // (s+0).eqv(s)
            Rational::axiom_eqv_transitive(
                r.add_spec(s),
                Rational::from_int_spec(0).add_spec(s),
                s.add_spec(Rational::from_int_spec(0)),
            );
            Rational::axiom_eqv_transitive(
                r.add_spec(s),
                s.add_spec(Rational::from_int_spec(0)),
                s,
            );
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            // add(Rat(r), Ext) = Ext(add(Rat(r), *re), im, d)
            // Need: eqv(Ext(add(Rat(r),*re), im, d), Ext(re, im, d))
            // = eqv(add(Rat(r),*re), *re) && eqv(*im, *im)
            lemma_dts_add_is_zero_left(DynTowerSpec::Rat(r), *re);
            lemma_dts_eqv_reflexive(*im);
        },
        (DynTowerSpec::Ext(re_x, im_x, d), DynTowerSpec::Ext(re_y, im_y, _)) => {
            // add(Ext_x, Ext_y) = Ext(add(re_x,re_y), add(im_x,im_y), d)
            // Need: eqv(Ext(add,add,d), Ext(re_y,im_y,d'))
            // = eqv(add(re_x,re_y), re_y) && eqv(add(im_x,im_y), im_y)
            lemma_dts_add_is_zero_left(*re_x, *re_y);
            lemma_dts_add_is_zero_left(*im_x, *im_y);
        },
        (DynTowerSpec::Ext(re_x, im_x, d), DynTowerSpec::Rat(r)) => {
            // add(Ext(re_x,im_x,d), Rat(r)) = Ext(add(re_x, Rat(r)), im_x, d)
            // Need: eqv(Ext(add(re_x,Rat(r)), im_x, d), Rat(r))
            // = eqv(add(re_x,Rat(r)), Rat(r)) && is_zero(im_x)
            lemma_dts_add_is_zero_left(*re_x, DynTowerSpec::Rat(r));
            // is_zero(im_x) from is_zero(Ext)
        },
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Equivalence lemmas
// ═══════════════════════════════════════════════════════════════════

pub proof fn lemma_dts_eqv_reflexive(a: DynTowerSpec)
    ensures dts_eqv(a, a),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            Rational::axiom_eqv_reflexive(r);
        },
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_eqv_reflexive(*re);
            lemma_dts_eqv_reflexive(*im);
        },
    }
}

pub proof fn lemma_dts_eqv_symmetric(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(a, b) == dts_eqv(b, a),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::axiom_eqv_symmetric(r1, r2);
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_eqv_symmetric(*re1, *re2);
            lemma_dts_eqv_symmetric(*im1, *im2);
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) => {
            // Forward: dts_eqv(Rat(r), *re) && is_zero(*im)
            // Backward: dts_eqv(*re, Rat(r)) && is_zero(*im)
            lemma_dts_eqv_symmetric(DynTowerSpec::Rat(r), *re);
        },
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) => {
            lemma_dts_eqv_symmetric(*re, DynTowerSpec::Rat(r));
        },
    }
}

pub proof fn lemma_dts_eqv_transitive(a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec)
    requires dts_eqv(a, b), dts_eqv(b, c),
    ensures dts_eqv(a, c),
    decreases a, b, c,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    Rational::axiom_eqv_transitive(r1, r2, r3);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // eqv(Rat(r2), Ext) = eqv(Rat(r2), *re3) && is_zero(*im3)
                    // Need eqv(Rat(r1), Ext) = eqv(Rat(r1), *re3) && is_zero(*im3)
                    lemma_dts_eqv_transitive(DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2), *re3);
                },
            }
        },
        (DynTowerSpec::Rat(r1), DynTowerSpec::Ext(re2, im2, _)) => {
            // eqv(Rat(r1), Ext) = eqv(Rat(r1), *re2) && is_zero(*im2)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // eqv(Ext, Rat(r3)) = eqv(*re2, Rat(r3)) && is_zero(*im2)
                    // Need eqv(Rat(r1), Rat(r3))
                    lemma_dts_eqv_transitive(DynTowerSpec::Rat(r1), *re2, DynTowerSpec::Rat(r3));
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // eqv(Ext2, Ext3) = eqv(*re2, *re3) && eqv(*im2, *im3)
                    // Need eqv(Rat(r1), Ext3) = eqv(Rat(r1), *re3) && is_zero(*im3)
                    lemma_dts_eqv_transitive(DynTowerSpec::Rat(r1), *re2, *re3);
                    lemma_dts_is_zero_congruence(*im2, *im3);
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Rat(r2)) => {
            // eqv(Ext, Rat(r2)) = eqv(*re1, Rat(r2)) && is_zero(*im1)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // eqv(Rat(r2), Rat(r3)) = r2.eqv(r3)
                    // Need eqv(Ext, Rat(r3)) = eqv(*re1, Rat(r3)) && is_zero(*im1)
                    lemma_dts_eqv_transitive(*re1, DynTowerSpec::Rat(r2), DynTowerSpec::Rat(r3));
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // eqv(Rat(r2), Ext3) = eqv(Rat(r2), *re3) && is_zero(*im3)
                    // Need eqv(Ext1, Ext3) = eqv(*re1, *re3) && eqv(*im1, *im3)
                    lemma_dts_eqv_transitive(*re1, DynTowerSpec::Rat(r2), *re3);
                    lemma_dts_is_zero_eqv(*im1, *im3);
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            // eqv(Ext1, Ext2) = eqv(*re1, *re2) && eqv(*im1, *im2)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // eqv(Ext2, Rat(r3)) = eqv(*re2, Rat(r3)) && is_zero(*im2)
                    // Need eqv(Ext1, Rat(r3)) = eqv(*re1, Rat(r3)) && is_zero(*im1)
                    lemma_dts_eqv_transitive(*re1, *re2, DynTowerSpec::Rat(r3));
                    lemma_dts_eqv_symmetric(*im1, *im2);
                    lemma_dts_is_zero_congruence(*im2, *im1);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    lemma_dts_eqv_transitive(*re1, *re2, *re3);
                    lemma_dts_eqv_transitive(*im1, *im2, *im3);
                },
            }
        },
    }
}

pub proof fn lemma_dts_eq_implies_eqv(a: DynTowerSpec, b: DynTowerSpec)
    requires a == b,
    ensures dts_eqv(a, b),
{
    lemma_dts_eqv_reflexive(a);
}

// ═══════════════════════════════════════════════════════════════════
//  Additive lemmas
// ═══════════════════════════════════════════════════════════════════

pub proof fn lemma_dts_add_commutative(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(dts_add(a, b), dts_add(b, a)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::axiom_add_commutative(r1, r2);
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_add_commutative(*re1, *re2);
            lemma_dts_add_commutative(*im1, *im2);
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            // add(Rat, Ext) = Ext(add(Rat(r),*re), im, d)
            // add(Ext, Rat) = Ext(add(*re,Rat(r)), im, d)
            lemma_dts_add_commutative(DynTowerSpec::Rat(r), *re);
            lemma_dts_eqv_reflexive(*im);
        },
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_add_commutative(*re, DynTowerSpec::Rat(r));
            lemma_dts_eqv_reflexive(*im);
        },
    }
}

pub proof fn lemma_dts_add_associative(a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec)
    ensures dts_eqv(dts_add(dts_add(a, b), c), dts_add(a, dts_add(b, c))),
    decreases a, b, c,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    Rational::axiom_add_associative(r1, r2, r3);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // LHS: add(Rat(r1+r2), Ext) = Ext(add(Rat(r1+r2), *re3), im3, d)
                    // RHS: add(Rat(r1), Ext(add(Rat(r2),*re3), im3, d)) = Ext(add(Rat(r1), add(Rat(r2),*re3)), im3, d)
                    lemma_dts_add_associative(DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2), *re3);
                    lemma_dts_eqv_reflexive(*im3);
                },
            }
        },
        (DynTowerSpec::Rat(r1), DynTowerSpec::Ext(re2, im2, d2)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    // LHS: add(Ext(add(Rat(r1),*re2), im2, d2), Rat(r3))
                    //     = Ext(add(add(Rat(r1),*re2), Rat(r3)), im2, d2)
                    // RHS: add(Rat(r1), Ext(add(*re2, Rat(r3)), im2, d2))
                    //     = Ext(add(Rat(r1), add(*re2, Rat(r3))), im2, d2)
                    lemma_dts_add_associative(DynTowerSpec::Rat(r1), *re2, DynTowerSpec::Rat(r3));
                    lemma_dts_eqv_reflexive(*im2);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // LHS: add(Ext(add(Rat(r1),*re2), im2, d2), Ext3)
                    //     = Ext(add(add(Rat(r1),*re2), *re3), add(im2, im3), d2)
                    // RHS: add(Rat(r1), Ext(add(*re2,*re3), add(im2,im3), d2))
                    //     = Ext(add(Rat(r1), add(*re2,*re3)), add(im2,im3), d2)
                    lemma_dts_add_associative(DynTowerSpec::Rat(r1), *re2, *re3);
                    lemma_dts_eqv_reflexive(dts_add(*im2, *im3));
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Rat(r2)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    // LHS: add(Ext(add(*re1,Rat(r2)),im1,d1), Rat(r3))
                    //     = Ext(add(add(*re1,Rat(r2)), Rat(r3)), im1, d1)
                    // RHS: add(Ext1, Rat(r2+r3))
                    //     = Ext(add(*re1, Rat(r2+r3)), im1, d1)
                    // Need: eqv(add(add(re1,R2),R3), add(re1, add(R2,R3)))
                    // where add(R2,R3) = Rat(r2+r3) by definition
                    lemma_dts_add_associative(*re1, DynTowerSpec::Rat(r2), DynTowerSpec::Rat(r3));
                    lemma_dts_eqv_reflexive(*im1);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // LHS: add(Ext(add(re1,R2),im1,d1), Ext3)
                    //     = Ext(add(add(re1,R2),re3), add(im1,im3), d1)
                    // RHS: add(Ext1, Ext(add(R2,re3),im3,d?))
                    //     = Ext(add(re1, add(R2,re3)), add(im1,im3), d1)
                    lemma_dts_add_associative(*re1, DynTowerSpec::Rat(r2), *re3);
                    lemma_dts_eqv_reflexive(dts_add(*im1, *im3));
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, _)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    // LHS: add(Ext(add(re1,re2),add(im1,im2),d1), Rat(r3))
                    //     = Ext(add(add(re1,re2),Rat(r3)), add(im1,im2), d1)
                    // RHS: add(Ext1, Ext(add(re2,Rat(r3)),im2,d2))
                    //     = Ext(add(re1,add(re2,Rat(r3))), add(im1,im2), d1)
                    lemma_dts_add_associative(*re1, *re2, DynTowerSpec::Rat(r3));
                    lemma_dts_eqv_reflexive(dts_add(*im1, *im2));
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    lemma_dts_add_associative(*re1, *re2, *re3);
                    lemma_dts_add_associative(*im1, *im2, *im3);
                },
            }
        },
    }
}

pub proof fn lemma_dts_add_zero_right(a: DynTowerSpec)
    ensures dts_eqv(dts_add(a, dts_zero()), a),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            Rational::axiom_add_zero_right(r);
        },
        DynTowerSpec::Ext(re, im, _) => {
            // add(Ext, Rat(0)) = Ext(add(*re, Rat(0)), im, d)
            // Need: eqv(add(*re,Rat(0)), *re) && eqv(*im, *im)
            lemma_dts_add_zero_right(*re);
            lemma_dts_eqv_reflexive(*im);
        },
    }
}

pub proof fn lemma_dts_add_congruence_left(a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec)
    requires dts_eqv(a, b),
    ensures dts_eqv(dts_add(a, c), dts_add(b, c)),
    decreases a, b, c,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            match c {
                DynTowerSpec::Rat(r3) => {
                    Rational::axiom_add_congruence_left(r1, r2, r3);
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // add(Rat(r1), Ext) = Ext(add(Rat(r1),*re3), im3, d)
                    // add(Rat(r2), Ext) = Ext(add(Rat(r2),*re3), im3, d)
                    lemma_dts_add_congruence_left(
                        DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2), *re3);
                    lemma_dts_eqv_reflexive(*im3);
                },
            }
        },
        (DynTowerSpec::Rat(r1), DynTowerSpec::Ext(re2, im2, _)) => {
            // eqv(Rat(r1), Ext2) = eqv(Rat(r1), *re2) && is_zero(*im2)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // add(Rat(r1), Rat(r3)) = Rat(r1+r3)
                    // add(Ext2, Rat(r3)) = Ext(add(*re2, Rat(r3)), im2, d2)
                    // Need eqv(Rat(r1+r3), Ext(add(*re2,R3), im2, d))
                    //   = eqv(Rat(r1+r3), add(*re2,R3)) && is_zero(*im2) ✓
                    lemma_dts_add_congruence_left(
                        DynTowerSpec::Rat(r1), *re2, DynTowerSpec::Rat(r3));
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // add(Rat(r1), Ext3) = Ext(add(Rat(r1),*re3), im3, d3)
                    // add(Ext2, Ext3) = Ext(add(*re2,*re3), add(*im2,*im3), d2)
                    // Need eqv(Ext(add(R1,re3),im3,d3), Ext(add(re2,re3),add(im2,im3),d2))
                    //   = eqv(add(R1,re3), add(re2,re3)) && eqv(im3, add(im2,im3))
                    lemma_dts_add_congruence_left(
                        DynTowerSpec::Rat(r1), *re2, *re3);
                    // For im: need eqv(*im3, add(*im2,*im3))
                    // Equivalently: add(zero, im3) ≡ add(im2, im3) where im2 is zero
                    // Use: is_zero(im2) ==> add(im2, im3) ≡ im3
                    lemma_dts_add_is_zero_left(*im2, *im3);
                    lemma_dts_eqv_symmetric(dts_add(*im2, *im3), *im3);
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Rat(r2)) => {
            // eqv(Ext1, Rat(r2)) = eqv(*re1, Rat(r2)) && is_zero(*im1)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // add(Ext1, Rat(r3)) = Ext(add(*re1, Rat(r3)), im1, d1)
                    // add(Rat(r2), Rat(r3)) = Rat(r2+r3)
                    // Need eqv(Ext(add(re1,R3),im1,d), Rat(r2+r3))
                    //   = eqv(add(re1,R3), Rat(r2+r3)) && is_zero(im1) ✓
                    lemma_dts_add_congruence_left(
                        *re1, DynTowerSpec::Rat(r2), DynTowerSpec::Rat(r3));
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    // add(Ext1, Ext3) = Ext(add(re1,re3), add(im1,im3), d1)
                    // add(Rat(r2), Ext3) = Ext(add(Rat(r2),re3), im3, d3)
                    // Need eqv(Ext(add(re1,re3),add(im1,im3),d1), Ext(add(R2,re3),im3,d3))
                    //   = eqv(add(re1,re3), add(R2,re3)) && eqv(add(im1,im3), im3)
                    lemma_dts_add_congruence_left(*re1, DynTowerSpec::Rat(r2), *re3);
                    // For im: is_zero(im1) ==> add(im1,im3) ≡ im3
                    lemma_dts_add_is_zero_left(*im1, *im3);
                },
            }
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            // eqv(Ext1, Ext2) = eqv(*re1, *re2) && eqv(*im1, *im2)
            match c {
                DynTowerSpec::Rat(r3) => {
                    // add(Ext1, Rat) = Ext(add(re1,R3), im1, d1)
                    // add(Ext2, Rat) = Ext(add(re2,R3), im2, d2)
                    lemma_dts_add_congruence_left(*re1, *re2, DynTowerSpec::Rat(r3));
                    // im: eqv(*im1, *im2) — already have from precondition
                },
                DynTowerSpec::Ext(re3, im3, _) => {
                    lemma_dts_add_congruence_left(*re1, *re2, *re3);
                    lemma_dts_add_congruence_left(*im1, *im2, *im3);
                },
            }
        },
    }
}

pub proof fn lemma_dts_neg_congruence(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_eqv(a, b),
    ensures dts_eqv(dts_neg(a), dts_neg(b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::axiom_neg_congruence(r1, r2);
        },
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_neg_congruence(*re1, *re2);
            lemma_dts_neg_congruence(*im1, *im2);
        },
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) => {
            // neg(Rat(r)) = Rat(-r)
            // neg(Ext(re,im,d)) = Ext(neg(*re), neg(*im), d)
            // eqv(Rat(-r), Ext(neg(*re), neg(*im), d))
            //   = eqv(Rat(-r), neg(*re)) && is_zero(neg(*im))
            // From eqv(Rat(r), *re), need eqv(Rat(-r), neg(*re)) — recurse
            lemma_dts_neg_congruence(DynTowerSpec::Rat(r), *re);
            // is_zero(neg(*im)) from is_zero(*im):
            // is_zero(*im) ==> all bottom rats are zero ==> negating still zero
            lemma_dts_neg_preserves_is_zero(*im);
        },
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) => {
            lemma_dts_neg_congruence(*re, DynTowerSpec::Rat(r));
            lemma_dts_neg_preserves_is_zero(*im);
        },
    }
}

/// Negation preserves is_zero.
pub proof fn lemma_dts_neg_preserves_is_zero(x: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_is_zero(dts_neg(x)),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => {
            // is_zero: r.eqv(0). neg: -r. Need (-r).eqv(0).
            // r.eqv(0) ==> -r.eqv(-0) ==> -r.eqv(0) (since -0 = 0)
            Rational::axiom_neg_congruence(r, Rational::from_int_spec(0));
            // Now: neg(r).eqv(neg(0))
            // neg(0) = from_int_spec(0).neg_spec() = ... need to show this is 0
            // Actually: Rational { num: 0, den: 0 }.neg_spec() = Rational { num: 0, den: 0 }
            // So neg(0) == 0. And neg(r).eqv(neg(0)) && neg(0)==0 ==> neg(r).eqv(0).
            Rational::axiom_eq_implies_eqv(
                Rational::from_int_spec(0).neg_spec(),
                Rational::from_int_spec(0),
            );
            Rational::axiom_eqv_transitive(
                r.neg_spec(),
                Rational::from_int_spec(0).neg_spec(),
                Rational::from_int_spec(0),
            );
        },
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_neg_preserves_is_zero(*re);
            lemma_dts_neg_preserves_is_zero(*im);
        },
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Multiplication congruence infrastructure
// ═══════════════════════════════════════════════════════════════════

/// If x is zero, then mul(c, x) is zero.


/// neg(a)*neg(b) ≡ a*b (product of negations).
/// Requires same_radicand and well-formed for the cross-component products.
pub proof fn lemma_dts_neg_mul_neg(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_same_radicand(a, b), dts_well_formed(a), dts_well_formed(b),
    ensures dts_eqv(dts_mul(dts_neg(a), dts_neg(b)), dts_mul(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            verus_algebra::lemmas::ring_lemmas::lemma_neg_mul_neg::<
                verus_rational::rational::Rational>(r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            let na_re = dts_neg(*re1); let na_im = dts_neg(*im1);
            let nb_re = dts_neg(*re2); let nb_im = dts_neg(*im2);
            // From well_formed: same_radicand(re1, im1) and same_radicand(re2, im2)
            // From precondition: same_radicand(re1, re2) and same_radicand(im1, im2)
            // Cross: same_radicand(re1, im2) by transitivity: re1~im1~im2
            lemma_dts_same_radicand_symmetric(*im1, *im2);
            lemma_dts_same_radicand_transitive(*re1, *im1, *im2);
            // Cross: same_radicand(im1, re2) by transitivity: im1~re1~re2... wait need im1~re1
            lemma_dts_same_radicand_symmetric(*re1, *im1);
            lemma_dts_same_radicand_transitive(*im1, *re1, *re2);
            // IH on all 4 pairs
            lemma_dts_neg_mul_neg(*re1, *re2);
            lemma_dts_neg_mul_neg(*im1, *im2);
            lemma_dts_neg_mul_neg(*re1, *im2);
            lemma_dts_neg_mul_neg(*im1, *re2);
            // RE: neg(re1)*neg(re2) + d*neg(im1)*neg(im2) ≡ re1*re2 + d*im1*im2
            // same_radicand(mul(na_im, nb_im), mul(im1, im2)) for mul_congruence
            // Chain: na_im~im1 [neg_symmetric], nb_im~im2 [neg_symmetric]
            lemma_dts_same_radicand_neg(*im1);
            lemma_dts_same_radicand_symmetric(*im1, na_im);
            lemma_dts_same_radicand_neg(*im2);
            lemma_dts_same_radicand_symmetric(*im2, nb_im);
            // mul_left: same_rad(na_im, im1) → same_rad(na_im*nb_im, im1*nb_im)
            lemma_dts_mul_preserves_same_radicand_left(na_im, *im1, nb_im);
            // mul_right: same_rad(nb_im, im2) → same_rad(im1*nb_im, im1*im2)
            lemma_dts_mul_preserves_same_radicand_right(nb_im, *im2, *im1);
            lemma_dts_same_radicand_transitive(
                dts_mul(na_im, nb_im), dts_mul(*im1, nb_im), dts_mul(*im1, *im2));
            lemma_dts_mul_congruence_right(dts_mul(na_im, nb_im), dts_mul(*im1, *im2), *d);
            lemma_dts_add_congruence_left(
                dts_mul(na_re, nb_re), dts_mul(*re1, *re2),
                dts_mul(*d, dts_mul(na_im, nb_im)));
            lemma_dts_add_congruence_right(
                dts_mul(*re1, *re2),
                dts_mul(*d, dts_mul(na_im, nb_im)),
                dts_mul(*d, dts_mul(*im1, *im2)));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(na_re, nb_re), dts_mul(*d, dts_mul(na_im, nb_im))),
                dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(na_im, nb_im))),
                dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2))));
            // IM: neg(re1)*neg(im2) + neg(im1)*neg(re2) ≡ re1*im2 + im1*re2
            lemma_dts_add_congruence_left(
                dts_mul(na_re, nb_im), dts_mul(*re1, *im2),
                dts_mul(na_im, nb_re));
            lemma_dts_add_congruence_right(
                dts_mul(*re1, *im2),
                dts_mul(na_im, nb_re),
                dts_mul(*im1, *re2));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(na_re, nb_im), dts_mul(na_im, nb_re)),
                dts_add(dts_mul(*re1, *im2), dts_mul(na_im, nb_re)),
                dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2)));
        }
        _ => {
            // Cross-depth: same_radicand(Rat, Ext) = false, requires is false
        }
    }
}

/// neg(a)² ≡ a² (squaring absorbs negation).
/// Requires well-formed: sub-components share radicand structure.
pub proof fn lemma_dts_neg_square(a: DynTowerSpec)
    requires dts_well_formed(a),
    ensures dts_eqv(dts_mul(dts_neg(a), dts_neg(a)), dts_mul(a, a)),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            verus_algebra::lemmas::ring_lemmas::lemma_neg_mul_neg::<
                verus_rational::rational::Rational>(r, r);
        }
        DynTowerSpec::Ext(re, im, d) => {
            let na = dts_neg(*re); let nb = dts_neg(*im);
            // IH: neg(re)² ≡ re², neg(im)² ≡ im²
            lemma_dts_neg_square(*re);
            lemma_dts_neg_square(*im);
            // d * neg(im)² ≡ d * im²
            // same_radicand(neg(im), im) → symmetric → same_radicand(im, neg(im))... wait
            // same_radicand_neg gives same_radicand(im, neg(im))
            // need same_radicand(neg(im), im) for mul_preserves
            lemma_dts_same_radicand_neg(*im);
            lemma_dts_same_radicand_symmetric(*im, nb);
            // Now: same_radicand(nb, im)
            lemma_dts_mul_preserves_same_radicand_left(nb, *im, nb);
            // same_radicand(nb*nb, im*nb)
            lemma_dts_mul_preserves_same_radicand_right(nb, *im, *im);
            // same_radicand(im*nb, im*im)
            lemma_dts_same_radicand_transitive(
                dts_mul(nb, nb), dts_mul(*im, nb), dts_mul(*im, *im));
            lemma_dts_mul_congruence_right(dts_mul(nb, nb), dts_mul(*im, *im), *d);
            // RE: neg(re)² + d*neg(im)² ≡ re² + d*im²
            lemma_dts_add_congruence_left(
                dts_mul(na, na), dts_mul(*re, *re),
                dts_mul(*d, dts_mul(nb, nb)));
            lemma_dts_add_congruence_right(
                dts_mul(*re, *re),
                dts_mul(*d, dts_mul(nb, nb)),
                dts_mul(*d, dts_mul(*im, *im)));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(na, na), dts_mul(*d, dts_mul(nb, nb))),
                dts_add(dts_mul(*re, *re), dts_mul(*d, dts_mul(nb, nb))),
                dts_add(dts_mul(*re, *re), dts_mul(*d, dts_mul(*im, *im))));
            // IM: neg(re)*neg(im) + neg(im)*neg(re) ≡ re*im + im*re
            // From well_formed(a): same_radicand(re, im). Use neg_mul_neg.
            lemma_dts_neg_mul_neg(*re, *im);
            lemma_dts_same_radicand_symmetric(*re, *im);
            lemma_dts_neg_mul_neg(*im, *re);
            lemma_dts_add_congruence_left(
                dts_mul(na, nb), dts_mul(*re, *im),
                dts_mul(nb, na));
            lemma_dts_add_congruence_right(
                dts_mul(*re, *im),
                dts_mul(nb, na),
                dts_mul(*im, *re));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(na, nb), dts_mul(nb, na)),
                dts_add(dts_mul(*re, *im), dts_mul(nb, na)),
                dts_add(dts_mul(*re, *im), dts_mul(*im, *re)));
        }
    }
}

/// Tower closure for add: same_radicand(a, b) ∧ same_radicand(a, c) ⟹ same_radicand(a, add(b, c)).
pub proof fn lemma_dts_same_radicand_closed_add(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_same_radicand(a, b), dts_same_radicand(a, c),
    ensures dts_same_radicand(a, dts_add(b, c)),
    decreases a, b, c,
{
    match (a, b, c) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(a_re, a_im, _),
         DynTowerSpec::Ext(b_re, b_im, _),
         DynTowerSpec::Ext(c_re, c_im, _)) => {
            lemma_dts_same_radicand_closed_add(*a_re, *b_re, *c_re);
            lemma_dts_same_radicand_closed_add(*a_im, *b_im, *c_im);
        }
        _ => {} // cross-depth: same_radicand(a,b) or same_radicand(a,c) is false
    }
}

/// Tower closure for mul: same_radicand(a, b) ∧ same_radicand(a, c) ∧ well_formed ⟹ same_radicand(a, mul(b, c)).
pub proof fn lemma_dts_same_radicand_closed_mul(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires
        dts_same_radicand(a, b), dts_same_radicand(a, c),
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
    ensures dts_same_radicand(a, dts_mul(b, c)),
    decreases a, b, c,
{
    match (a, b, c) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(a_re, a_im, _),
         DynTowerSpec::Ext(b_re, b_im, d_b),
         DynTowerSpec::Ext(c_re, c_im, _)) => {
            // mul(b, c) = Ext(b_re*c_re + d_b*b_im*c_im, b_re*c_im + b_im*c_re, d_b)
            // Need: same_rad(a_re, re_product) and same_rad(a_im, im_product)
            // From same_rad(a,b): a_re~b_re, a_im~b_im
            // From same_rad(a,c): a_re~c_re, a_im~c_im
            // From well_formed(b): b_re~b_im, b_re~d_b
            // a_re ~ b_re ~ d_b (by transitivity)
            lemma_dts_same_radicand_transitive(*a_re, *b_re, *d_b);
            // Cross: a_re ~ b_im (from a_re~a_im and a_im~b_im? No: a_re~b_re, well_formed(a)→a_re~a_im, a_im~b_im)
            // Actually from well_formed(a): a_re ~ a_im. From same_rad(a,b): a_im ~ b_im.
            // So a_re ~ b_im by transitivity.
            lemma_dts_same_radicand_transitive(*a_re, *a_im, *b_im);
            // a_re ~ c_im (from a_re ~ a_im ~ c_im)
            lemma_dts_same_radicand_transitive(*a_re, *a_im, *c_im);

            // IH for sub-products: a_re ~ mul(b_re, c_re)
            lemma_dts_same_radicand_closed_mul(*a_re, *b_re, *c_re);
            // a_re ~ mul(b_im, c_im)
            lemma_dts_same_radicand_closed_mul(*a_re, *b_im, *c_im);
            // a_re ~ mul(d_b, mul(b_im, c_im)): need well_formed(mul(b_im, c_im))
            lemma_dts_mul_well_formed(*b_im, *c_im);
            lemma_dts_same_radicand_closed_mul(*a_re, *d_b, dts_mul(*b_im, *c_im));
            // a_re ~ add(b_re*c_re, d_b*b_im*c_im)
            lemma_dts_same_radicand_closed_add(
                *a_re, dts_mul(*b_re, *c_re), dts_mul(*d_b, dts_mul(*b_im, *c_im)));

            // im_product: b_re*c_im + b_im*c_re
            // a_im ~ b_re (from a_im ~ a_re ~ b_re)
            lemma_dts_same_radicand_symmetric(*a_re, *a_im);
            lemma_dts_same_radicand_transitive(*a_im, *a_re, *b_re);
            lemma_dts_same_radicand_transitive(*a_im, *a_re, *c_re);
            // a_im ~ c_im (from same_rad(a,c))
            // a_im ~ b_im (from same_rad(a,b))
            lemma_dts_same_radicand_closed_mul(*a_im, *b_re, *c_im);
            lemma_dts_same_radicand_closed_mul(*a_im, *b_im, *c_re);
            lemma_dts_same_radicand_closed_add(
                *a_im, dts_mul(*b_re, *c_im), dts_mul(*b_im, *c_re));
        }
        _ => {} // cross-depth: same_radicand is false
    }
}

/// neg preserves well-formedness.
pub proof fn lemma_dts_neg_well_formed(a: DynTowerSpec)
    requires dts_well_formed(a),
    ensures dts_well_formed(dts_neg(a)),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(_) => {}
        DynTowerSpec::Ext(re, im, d) => {
            lemma_dts_neg_well_formed(*re);
            lemma_dts_neg_well_formed(*im);
            lemma_dts_neg_preserves_same_radicand(*re, *im);
            // same_radicand(neg(re), d): from re~d, neg preserves → neg(re)~neg(d)?
            // No: same_radicand(re, d) from well_formed. neg(re) ~ re [neg_same_rad].
            // symmetric: re ~ neg(re). Then neg(re) ~ d by: neg(re) ~ re ~ d.
            lemma_dts_same_radicand_neg(*re);
            lemma_dts_same_radicand_symmetric(*re, dts_neg(*re));
            lemma_dts_same_radicand_transitive(dts_neg(*re), *re, *d);
        }
    }
}

/// mul preserves well-formedness (when operands have same radicand).
pub proof fn lemma_dts_mul_well_formed(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures dts_well_formed(dts_mul(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            // Products of sub-components
            // From well_formed: same_rad(re1,im1), same_rad(re2,im2)
            // From precondition: same_rad(re1,re2), same_rad(im1,im2)
            // Cross: same_rad(re1,im2) and same_rad(im1,re2)
            lemma_dts_same_radicand_symmetric(*im1, *im2);
            lemma_dts_same_radicand_transitive(*re1, *im1, *im2);
            lemma_dts_same_radicand_symmetric(*re1, *im1);
            lemma_dts_same_radicand_transitive(*im1, *re1, *re2);
            // All 4 sub-products are well-formed + same_radicand
            lemma_dts_mul_well_formed(*re1, *re2);
            lemma_dts_mul_well_formed(*im1, *im2);
            lemma_dts_mul_well_formed(*re1, *im2);
            lemma_dts_mul_well_formed(*im1, *re2);
            // same_radicand(d, mul(im1, im2)) via closed_mul
            lemma_dts_same_radicand_symmetric(*re1, *d);
            lemma_dts_same_radicand_transitive(*d, *re1, *im1);
            lemma_dts_same_radicand_transitive(*d, *im1, *im2);
            lemma_dts_same_radicand_closed_mul(*d, *im1, *im2);
            // d * mul(im1,im2) well-formed
            lemma_dts_mul_well_formed(*d, dts_mul(*im1, *im2));
            // same_radicand(re1*re2, d*im1*im2) via closed_mul on re1
            lemma_dts_same_radicand_reflexive(*re1);
            lemma_dts_same_radicand_closed_mul(*re1, *re1, *re2);
            lemma_dts_same_radicand_transitive(*re1, *d, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_closed_mul(*re1, *d, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_closed_add(
                *re1, dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            // Need: same_radicand(re1, re_product) → same_radicand(re_product, d)
            // For well_formed of the result Ext: need same_radicand(re_product, im_product) and same_radicand(re_product, d)
            // re_product ~ re1 [from closed_add]. re1 ~ d [from well_formed(a)]. So re_product ~ d.
            lemma_dts_same_radicand_symmetric(*re1,
                dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2))));
            lemma_dts_same_radicand_transitive(
                dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2))),
                *re1, *d);
            // same_radicand(re1*im2, im1*re2) for add_well_formed
            lemma_dts_same_radicand_closed_mul(*re1, *re1, *im2);  // re1 already reflexive from above
            lemma_dts_same_radicand_transitive(*re1, *im1, *re2);
            lemma_dts_same_radicand_closed_mul(*re1, *im1, *re2);
            lemma_dts_same_radicand_closed_add(
                *re1, dts_mul(*re1, *im2), dts_mul(*im1, *re2));
            lemma_dts_add_well_formed(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            lemma_dts_add_well_formed(dts_mul(*re1, *im2), dts_mul(*im1, *re2));
            // same_radicand(re_product, im_product)
            lemma_dts_same_radicand_symmetric(*re1,
                dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2)));
            lemma_dts_same_radicand_transitive(
                dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2))),
                *re1,
                dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2)));
        }
        (DynTowerSpec::Rat(_), DynTowerSpec::Ext(re, im, _)) => {
            lemma_dts_mul_well_formed(a, *re);
            lemma_dts_mul_well_formed(a, *im);
        }
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(_)) => {
            lemma_dts_mul_well_formed(*re, b);
            lemma_dts_mul_well_formed(*im, b);
        }
    }
}

/// add preserves well-formedness (when operands have same radicand).
pub proof fn lemma_dts_add_well_formed(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures dts_well_formed(dts_add(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_add_well_formed(*re1, *re2);
            lemma_dts_add_well_formed(*im1, *im2);
            lemma_dts_add_preserves_same_radicand_both(*re1, *re2, *im1, *im2);
            // same_radicand(add(re1,re2), d1):
            // re1 ~ d1 [from well_formed(a)], re2 ~ d1 [re2 ~ re1 ~ ... same_rad chain]
            // Actually d1 from a's Ext. From same_radicand(a, b): d1 == d_b. well_formed(b): re2 ~ d_b.
            // So re2 ~ d1. And re1 ~ d1.
            // add(re1, re2) ~ d1 by closed_add(d1, re1, re2)? No, closed_add(a, b, c) gives same_rad(a, add(b,c)).
            lemma_dts_same_radicand_symmetric(*re1, *d1);
            lemma_dts_same_radicand_transitive(*d1, *re1, *re2);
            lemma_dts_same_radicand_closed_add(*d1, *re1, *re2);
            lemma_dts_same_radicand_symmetric(*d1, dts_add(*re1, *re2));
        }
        (DynTowerSpec::Rat(_), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_add_well_formed(a, *re);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(_)) => {
            lemma_dts_add_well_formed(*re, b);
        }
    }
}

/// neg(neg(x)) ≡ x (double negation / involution).
pub proof fn lemma_dts_neg_involution(x: DynTowerSpec)
    ensures dts_eqv(dts_neg(dts_neg(x)), x),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => {
            verus_algebra::lemmas::additive_group_lemmas::lemma_neg_involution::<
                verus_rational::rational::Rational>(r);
        }
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_neg_involution(*re);
            lemma_dts_neg_involution(*im);
        }
    }
}

pub proof fn lemma_dts_mul_is_zero_right(x: DynTowerSpec, c: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_is_zero(dts_mul(c, x)),
    decreases c, x,
{
    match (c, x) {
        (DynTowerSpec::Rat(rc), DynTowerSpec::Rat(rx)) => {
            // mul(Rat(rc), Rat(rx)) = Rat(rc * rx)
            // is_zero(Rat(rx)): rx.eqv(0)
            // Need: (rc * rx).eqv(0)
            use verus_rational::rational::Rational;
            let zero = Rational::from_int_spec(0);
            // rx.eqv(0) → mul(rx, rc).eqv(mul(0, rc)) by mul_congruence_left
            Rational::axiom_mul_congruence_left(rx, zero, rc);
            // mul(0, rc).eqv(0) by mul_zero_left
            verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<Rational>(rc);
            // Chain: mul(rx, rc).eqv(0)
            Rational::axiom_eqv_transitive(rx.mul_spec(rc), zero.mul_spec(rc), zero);
            // mul(rc, rx) ≡ mul(rx, rc) by commutativity
            Rational::axiom_mul_commutative(rc, rx);
            // Chain: mul(rc, rx).eqv(0)
            Rational::axiom_eqv_transitive(rc.mul_spec(rx), rx.mul_spec(rc), zero);
        },
        (DynTowerSpec::Rat(rc), DynTowerSpec::Ext(re_x, im_x, _)) => {
            // mul(Rat(rc), Ext_x) = Ext(mul(Rat(rc), re_x), mul(Rat(rc), im_x), d_x)
            // is_zero(Ext_x): is_zero(re_x) && is_zero(im_x)
            lemma_dts_mul_is_zero_right(*re_x, DynTowerSpec::Rat(rc));
            lemma_dts_mul_is_zero_right(*im_x, DynTowerSpec::Rat(rc));
        },
        (DynTowerSpec::Ext(re_c, im_c, d_c), DynTowerSpec::Rat(rx)) => {
            // mul(Ext_c, Rat(rx)) = Ext(mul(re_c, Rat(rx)), mul(im_c, Rat(rx)), d_c)
            // is_zero(Rat(rx)): rx.eqv(0)
            lemma_dts_mul_is_zero_right(DynTowerSpec::Rat(rx), *re_c);
            lemma_dts_mul_is_zero_right(DynTowerSpec::Rat(rx), *im_c);
        },
        (DynTowerSpec::Ext(re_c, im_c, d_c), DynTowerSpec::Ext(re_x, im_x, _)) => {
            // mul(Ext_c, Ext_x) = Ext(
            //   add(mul(re_c,re_x), mul(d_c, mul(im_c,im_x))),
            //   add(mul(re_c,im_x), mul(im_c,re_x)),
            //   d_c)
            // is_zero(Ext_x): is_zero(re_x) && is_zero(im_x)
            // re component:
            lemma_dts_mul_is_zero_right(*re_x, *re_c);     // is_zero(mul(re_c, re_x))
            lemma_dts_mul_is_zero_right(*im_x, *im_c);     // is_zero(mul(im_c, im_x))
            lemma_dts_mul_is_zero_right(dts_mul(*im_c, *im_x), *d_c); // is_zero(mul(d_c, ...))
            lemma_dts_add_both_zero(
                dts_mul(*re_c, *re_x),
                dts_mul(*d_c, dts_mul(*im_c, *im_x)));
            // im component:
            lemma_dts_mul_is_zero_right(*im_x, *re_c);     // is_zero(mul(re_c, im_x))
            lemma_dts_mul_is_zero_right(*re_x, *im_c);     // is_zero(mul(im_c, re_x))
            lemma_dts_add_both_zero(
                dts_mul(*re_c, *im_x),
                dts_mul(*im_c, *re_x));
        },
    }
}

/// If x is zero, then mul(x, c) is zero (left version).
pub proof fn lemma_dts_mul_is_zero_left(x: DynTowerSpec, c: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_is_zero(dts_mul(x, c)),
    decreases x, c,
{
    match (x, c) {
        (DynTowerSpec::Rat(rx), DynTowerSpec::Rat(rc)) => {
            use verus_rational::rational::Rational;
            let zero = Rational::from_int_spec(0);
            Rational::axiom_mul_congruence_left(rx, zero, rc);
            verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<Rational>(rc);
            Rational::axiom_eqv_transitive(rx.mul_spec(rc), zero.mul_spec(rc), zero);
        },
        (DynTowerSpec::Rat(rx), DynTowerSpec::Ext(re_c, im_c, _)) => {
            // mul(Rat(rx), Ext_c) = Ext(mul(Rat(rx), re_c), mul(Rat(rx), im_c), d_c)
            lemma_dts_mul_is_zero_left(DynTowerSpec::Rat(rx), *re_c);
            lemma_dts_mul_is_zero_left(DynTowerSpec::Rat(rx), *im_c);
        },
        (DynTowerSpec::Ext(re_x, im_x, d_x), DynTowerSpec::Rat(rc)) => {
            // mul(Ext_x, Rat(rc)) = Ext(mul(re_x, Rat(rc)), mul(im_x, Rat(rc)), d_x)
            lemma_dts_mul_is_zero_left(*re_x, DynTowerSpec::Rat(rc));
            lemma_dts_mul_is_zero_left(*im_x, DynTowerSpec::Rat(rc));
        },
        (DynTowerSpec::Ext(re_x, im_x, d_x), DynTowerSpec::Ext(re_c, im_c, _)) => {
            // re: add(mul(re_x,re_c), mul(d_x, mul(im_x,im_c)))
            lemma_dts_mul_is_zero_left(*re_x, *re_c);
            lemma_dts_mul_is_zero_left(*im_x, *im_c);
            // mul(d_x, mul(im_x,im_c)): im_x*im_c is zero (just proved),
            // so use mul_is_zero_right for d_x * (zero result)
            lemma_dts_mul_is_zero_right(dts_mul(*im_x, *im_c), *d_x);
            lemma_dts_add_both_zero(
                dts_mul(*re_x, *re_c),
                dts_mul(*d_x, dts_mul(*im_x, *im_c)));
            // im: add(mul(re_x,im_c), mul(im_x,re_c))
            lemma_dts_mul_is_zero_left(*re_x, *im_c);
            lemma_dts_mul_is_zero_left(*im_x, *re_c);
            lemma_dts_add_both_zero(
                dts_mul(*re_x, *im_c),
                dts_mul(*im_x, *re_c));
        },
    }
}

/// add preserves same_radicand (both): if same_radicand(a1, a2) && same_radicand(b1, b2)
/// then same_radicand(add(a1, b1), add(a2, b2)).
pub proof fn lemma_dts_add_preserves_same_radicand_both(
    a1: DynTowerSpec, a2: DynTowerSpec, b1: DynTowerSpec, b2: DynTowerSpec,
)
    requires dts_same_radicand(a1, a2), dts_same_radicand(b1, b2),
    ensures dts_same_radicand(dts_add(a1, b1), dts_add(a2, b2)),
    decreases a1, a2, b1, b2,
{
    // same_radicand is false for cross-depth, so a1/a2 must be same variant
    // and b1/b2 must be same variant. This gives 4 cases.
    match (a1, a2) {
        (DynTowerSpec::Rat(ra1), DynTowerSpec::Rat(ra2)) => {
            match (b1, b2) {
                (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {
                    // Rat+Rat=Rat × Rat+Rat=Rat → same_radicand(Rat,Rat)=true ✓
                },
                (DynTowerSpec::Ext(re_b1, _, _), DynTowerSpec::Ext(re_b2, _, _)) => {
                    // add(Rat,Ext) = Ext(add(Rat,re_b), im_b, d_b) for both
                    // d_b1 == d_b2 from same_radicand(b1,b2) ✓
                    lemma_dts_add_preserves_same_radicand_both(
                        DynTowerSpec::Rat(ra1), DynTowerSpec::Rat(ra2), *re_b1, *re_b2);
                },
                _ => {}, // cross-depth b: unreachable (same_radicand = false)
            }
        },
        (DynTowerSpec::Ext(re_a1, im_a1, _), DynTowerSpec::Ext(re_a2, im_a2, _)) => {
            match (b1, b2) {
                (DynTowerSpec::Rat(rb1), DynTowerSpec::Rat(rb2)) => {
                    // add(Ext,Rat) = Ext(add(re_a,Rat), im_a, d_a) for both
                    // d_a1 == d_a2 ✓
                    lemma_dts_add_preserves_same_radicand_both(
                        *re_a1, *re_a2, DynTowerSpec::Rat(rb1), DynTowerSpec::Rat(rb2));
                },
                (DynTowerSpec::Ext(re_b1, im_b1, _), DynTowerSpec::Ext(re_b2, im_b2, _)) => {
                    // add(Ext,Ext) = Ext(add(re_a,re_b), add(im_a,im_b), d_a) for both
                    // d_a1 == d_a2 ✓
                    lemma_dts_add_preserves_same_radicand_both(*re_a1, *re_a2, *re_b1, *re_b2);
                    lemma_dts_add_preserves_same_radicand_both(*im_a1, *im_a2, *im_b1, *im_b2);
                },
                _ => {}, // cross-depth b: unreachable
            }
        },
        _ => {}, // cross-depth a: unreachable (same_radicand = false)
    }
}

/// mul preserves same_radicand (right): if same_radicand(a, b) then same_radicand(mul(c, a), mul(c, b)).
pub proof fn lemma_dts_mul_preserves_same_radicand_right(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_same_radicand(a, b),
    ensures dts_same_radicand(dts_mul(c, a), dts_mul(c, b)),
    decreases c, a, b,
{
    // same_radicand(a, b) with cross-depth = false means a,b are same variant.
    match (a, b) {
        (DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb)) => {
            match c {
                DynTowerSpec::Rat(_) => {
                    // mul(Rat,Rat)=Rat for both → same_radicand(Rat,Rat)=true ✓
                },
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    // mul(Ext_c, Rat_a) = Ext(mul(re_c,Rat_a), mul(im_c,Rat_a), d_c)
                    // mul(Ext_c, Rat_b) = Ext(mul(re_c,Rat_b), mul(im_c,Rat_b), d_c)
                    // same d_c ✓
                    lemma_dts_mul_preserves_same_radicand_right(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *im_c);
                },
            }
        },
        (DynTowerSpec::Ext(re_a, im_a, _), DynTowerSpec::Ext(re_b, im_b, _)) => {
            // same_radicand: d_a == d_b, same_radicand(re_a, re_b), same_radicand(im_a, im_b)
            match c {
                DynTowerSpec::Rat(rc) => {
                    // mul(Rat, Ext_a) = Ext(mul(Rat,re_a), mul(Rat,im_a), d_a)
                    // mul(Rat, Ext_b) = Ext(mul(Rat,re_b), mul(Rat,im_b), d_b)
                    // d_a == d_b ✓
                    lemma_dts_mul_preserves_same_radicand_right(
                        *re_a, *re_b, DynTowerSpec::Rat(rc));
                    lemma_dts_mul_preserves_same_radicand_right(
                        *im_a, *im_b, DynTowerSpec::Rat(rc));
                },
                DynTowerSpec::Ext(re_c, im_c, d_c) => {
                    // mul(Ext_c, Ext_a) = Ext(add(re_c*re_a, d_c*(im_c*im_a)),
                    //                         add(re_c*im_a, im_c*re_a), d_c)
                    // mul(Ext_c, Ext_b) = Ext(add(re_c*re_b, d_c*(im_c*im_b)),
                    //                         add(re_c*im_b, im_c*re_b), d_c)
                    // same d_c ✓. Need same_radicand for re and im sub-components.
                    // re sub-terms:
                    lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *im_c);
                    lemma_dts_mul_preserves_same_radicand_right(
                        dts_mul(*im_c, *im_a), dts_mul(*im_c, *im_b), *d_c);
                    lemma_dts_add_preserves_same_radicand_both(
                        dts_mul(*re_c, *re_a), dts_mul(*re_c, *re_b),
                        dts_mul(*d_c, dts_mul(*im_c, *im_a)),
                        dts_mul(*d_c, dts_mul(*im_c, *im_b)));
                    // im sub-terms:
                    lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *im_c);
                    lemma_dts_add_preserves_same_radicand_both(
                        dts_mul(*re_c, *im_a), dts_mul(*re_c, *im_b),
                        dts_mul(*im_c, *re_a), dts_mul(*im_c, *re_b));
                },
            }
        },
        _ => {}, // cross-depth: unreachable (same_radicand = false)
    }
}

/// Multiplication congruence (right): if eqv(a, b) && same_radicand(a, b)
/// then eqv(mul(c, a), mul(c, b)).
pub proof fn lemma_dts_mul_congruence_right(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_eqv(a, b), dts_same_radicand(a, b),
    ensures dts_eqv(dts_mul(c, a), dts_mul(c, b)),
    decreases c, a, b,
{
    // same_radicand false for cross-depth, so a,b are same variant.
    match (a, b) {
        (DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb)) => {
            // eqv(Rat(ra), Rat(rb)): ra.eqv(rb)
            match c {
                DynTowerSpec::Rat(rc) => {
                    // mul(Rat(rc), Rat(ra)) = Rat(rc*ra), mul(Rat(rc), Rat(rb)) = Rat(rc*rb)
                    // Need: eqv(rc*ra, rc*rb)
                    Rational::axiom_mul_commutative(rc, ra);
                    Rational::axiom_mul_commutative(rc, rb);
                    Rational::axiom_mul_congruence_left(ra, rb, rc);
                    // ra*rc ≡ rb*rc, rc*ra ≡ ra*rc, rc*rb ≡ rb*rc
                    Rational::axiom_eqv_transitive(rc.mul_spec(ra), ra.mul_spec(rc), rb.mul_spec(rc));
                    Rational::axiom_eqv_transitive(rc.mul_spec(ra), rb.mul_spec(rc), rc.mul_spec(rb));
                },
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    // mul(Ext_c, Rat_a) = Ext(mul(re_c,Rat_a), mul(im_c,Rat_a), d_c)
                    // mul(Ext_c, Rat_b) = Ext(mul(re_c,Rat_b), mul(im_c,Rat_b), d_c)
                    lemma_dts_mul_congruence_right(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *re_c);
                    lemma_dts_mul_congruence_right(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *im_c);
                },
            }
        },
        (DynTowerSpec::Ext(re_a, im_a, _), DynTowerSpec::Ext(re_b, im_b, _)) => {
            // eqv: eqv(re_a, re_b) && eqv(im_a, im_b)
            // same_radicand: d_a == d_b, same_radicand(re_a, re_b), same_radicand(im_a, im_b)
            match c {
                DynTowerSpec::Rat(rc) => {
                    // mul(Rat(rc), Ext_a) = Ext(mul(Rat(rc),re_a), mul(Rat(rc),im_a), d_a)
                    // mul(Rat(rc), Ext_b) = Ext(mul(Rat(rc),re_b), mul(Rat(rc),im_b), d_b)
                    // d_a == d_b ✓
                    lemma_dts_mul_congruence_right(
                        *re_a, *re_b, DynTowerSpec::Rat(rc));
                    lemma_dts_mul_congruence_right(
                        *im_a, *im_b, DynTowerSpec::Rat(rc));
                },
                DynTowerSpec::Ext(re_c, im_c, d_c) => {
                    // mul(Ext_c, Ext_a) = Ext(
                    //   add(mul(re_c,re_a), mul(d_c, mul(im_c,im_a))),
                    //   add(mul(re_c,im_a), mul(im_c,re_a)),
                    //   d_c)
                    // mul(Ext_c, Ext_b) = similar with re_b, im_b
                    // same d_c on both sides ✓

                    // re component congruence:
                    // eqv(mul(re_c,re_a), mul(re_c,re_b)) by recursive congruence
                    lemma_dts_mul_congruence_right(*re_a, *re_b, *re_c);
                    // eqv(mul(im_c,im_a), mul(im_c,im_b)) by recursive congruence
                    lemma_dts_mul_congruence_right(*im_a, *im_b, *im_c);
                    // same_radicand preserved for d_c * (im_c*im_...)
                    lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *im_c);
                    // eqv(mul(d_c, mul(im_c,im_a)), mul(d_c, mul(im_c,im_b)))
                    lemma_dts_mul_congruence_right(
                        dts_mul(*im_c, *im_a), dts_mul(*im_c, *im_b), *d_c);
                    // add congruence for re
                    lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(
                        dts_mul(*im_c, *im_a), dts_mul(*im_c, *im_b), *d_c);
                    lemma_dts_add_congruence_left(
                        dts_mul(*re_c, *re_a), dts_mul(*re_c, *re_b),
                        dts_mul(*d_c, dts_mul(*im_c, *im_a)));
                    lemma_dts_add_congruence_right(
                        dts_mul(*re_c, *re_b),
                        dts_mul(*d_c, dts_mul(*im_c, *im_a)),
                        dts_mul(*d_c, dts_mul(*im_c, *im_b)));
                    lemma_dts_eqv_transitive(
                        dts_add(dts_mul(*re_c, *re_a), dts_mul(*d_c, dts_mul(*im_c, *im_a))),
                        dts_add(dts_mul(*re_c, *re_b), dts_mul(*d_c, dts_mul(*im_c, *im_a))),
                        dts_add(dts_mul(*re_c, *re_b), dts_mul(*d_c, dts_mul(*im_c, *im_b))));

                    // im component congruence:
                    lemma_dts_mul_congruence_right(*im_a, *im_b, *re_c);
                    lemma_dts_mul_congruence_right(*re_a, *re_b, *im_c);
                    lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *im_c);
                    lemma_dts_add_congruence_left(
                        dts_mul(*re_c, *im_a), dts_mul(*re_c, *im_b),
                        dts_mul(*im_c, *re_a));
                    lemma_dts_add_congruence_right(
                        dts_mul(*re_c, *im_b),
                        dts_mul(*im_c, *re_a),
                        dts_mul(*im_c, *re_b));
                    lemma_dts_eqv_transitive(
                        dts_add(dts_mul(*re_c, *im_a), dts_mul(*im_c, *re_a)),
                        dts_add(dts_mul(*re_c, *im_b), dts_mul(*im_c, *re_a)),
                        dts_add(dts_mul(*re_c, *im_b), dts_mul(*im_c, *re_b)));
                },
            }
        },
        _ => {}, // cross-depth: unreachable
    }
}

/// Multiplication congruence (left): if eqv(a, b) && same_radicand(a, b)
/// then eqv(mul(a, c), mul(b, c)).
pub proof fn lemma_dts_mul_congruence_left(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_eqv(a, b), dts_same_radicand(a, b),
    ensures dts_eqv(dts_mul(a, c), dts_mul(b, c)),
    decreases a, b, c,
{
    match (a, b) {
        (DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb)) => {
            match c {
                DynTowerSpec::Rat(rc) => {
                    Rational::axiom_mul_congruence_left(ra, rb, rc);
                },
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    // mul(Rat_a, Ext_c) = Ext(mul(Rat_a,re_c), mul(Rat_a,im_c), d_c)
                    // mul(Rat_b, Ext_c) = Ext(mul(Rat_b,re_c), mul(Rat_b,im_c), d_c)
                    lemma_dts_mul_congruence_left(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *re_c);
                    lemma_dts_mul_congruence_left(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *im_c);
                },
            }
        },
        (DynTowerSpec::Ext(re_a, im_a, d_a), DynTowerSpec::Ext(re_b, im_b, _)) => {
            // d_a == d_b, same_radicand(re_a, re_b), same_radicand(im_a, im_b)
            match c {
                DynTowerSpec::Rat(rc) => {
                    // mul(Ext_a, Rat) = Ext(mul(re_a,Rat), mul(im_a,Rat), d_a)
                    // mul(Ext_b, Rat) = Ext(mul(re_b,Rat), mul(im_b,Rat), d_b)
                    lemma_dts_mul_congruence_left(
                        *re_a, *re_b, DynTowerSpec::Rat(rc));
                    lemma_dts_mul_congruence_left(
                        *im_a, *im_b, DynTowerSpec::Rat(rc));
                },
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    // mul(Ext_a, Ext_c) = Ext(
                    //   add(mul(re_a,re_c), mul(d_a, mul(im_a,im_c))),
                    //   add(mul(re_a,im_c), mul(im_a,re_c)),
                    //   d_a)
                    // mul(Ext_b, Ext_c) = similar with d_b == d_a

                    // re: congruence of re_a*re_c vs re_b*re_c
                    lemma_dts_mul_congruence_left(*re_a, *re_b, *re_c);
                    // re: congruence of im_a*im_c vs im_b*im_c
                    lemma_dts_mul_congruence_left(*im_a, *im_b, *im_c);
                    // re: d_a * (im_a*im_c) vs d_a * (im_b*im_c) — d_a == d_b structurally
                    lemma_dts_mul_preserves_same_radicand_left(*im_a, *im_b, *im_c);
                    lemma_dts_mul_congruence_right(
                        dts_mul(*im_a, *im_c), dts_mul(*im_b, *im_c), *d_a);
                    // add congruence for re
                    lemma_dts_mul_preserves_same_radicand_left(*re_a, *re_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_right(
                        dts_mul(*im_a, *im_c), dts_mul(*im_b, *im_c), *d_a);
                    lemma_dts_add_congruence_left(
                        dts_mul(*re_a, *re_c), dts_mul(*re_b, *re_c),
                        dts_mul(*d_a, dts_mul(*im_a, *im_c)));
                    lemma_dts_add_congruence_right(
                        dts_mul(*re_b, *re_c),
                        dts_mul(*d_a, dts_mul(*im_a, *im_c)),
                        dts_mul(*d_a, dts_mul(*im_b, *im_c)));
                    lemma_dts_eqv_transitive(
                        dts_add(dts_mul(*re_a, *re_c), dts_mul(*d_a, dts_mul(*im_a, *im_c))),
                        dts_add(dts_mul(*re_b, *re_c), dts_mul(*d_a, dts_mul(*im_a, *im_c))),
                        dts_add(dts_mul(*re_b, *re_c), dts_mul(*d_a, dts_mul(*im_b, *im_c))));

                    // im: congruence of re_a*im_c vs re_b*im_c
                    lemma_dts_mul_congruence_left(*re_a, *re_b, *im_c);
                    // im: congruence of im_a*re_c vs im_b*re_c
                    lemma_dts_mul_congruence_left(*im_a, *im_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_left(*re_a, *re_b, *im_c);
                    lemma_dts_mul_preserves_same_radicand_left(*im_a, *im_b, *re_c);
                    lemma_dts_add_congruence_left(
                        dts_mul(*re_a, *im_c), dts_mul(*re_b, *im_c),
                        dts_mul(*im_a, *re_c));
                    lemma_dts_add_congruence_right(
                        dts_mul(*re_b, *im_c),
                        dts_mul(*im_a, *re_c),
                        dts_mul(*im_b, *re_c));
                    lemma_dts_eqv_transitive(
                        dts_add(dts_mul(*re_a, *im_c), dts_mul(*im_a, *re_c)),
                        dts_add(dts_mul(*re_b, *im_c), dts_mul(*im_a, *re_c)),
                        dts_add(dts_mul(*re_b, *im_c), dts_mul(*im_b, *re_c)));
                },
            }
        },
        _ => {},
    }
}

/// mul preserves same_radicand (left): if same_radicand(a, b) then same_radicand(mul(a, c), mul(b, c)).
pub proof fn lemma_dts_mul_preserves_same_radicand_left(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_same_radicand(a, b),
    ensures dts_same_radicand(dts_mul(a, c), dts_mul(b, c)),
    decreases a, b, c,
{
    match (a, b) {
        (DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb)) => {
            match c {
                DynTowerSpec::Rat(_) => {},
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    lemma_dts_mul_preserves_same_radicand_left(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *re_c);
                    lemma_dts_mul_preserves_same_radicand_left(
                        DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *im_c);
                },
            }
        },
        (DynTowerSpec::Ext(re_a, im_a, d_a), DynTowerSpec::Ext(re_b, im_b, _)) => {
            match c {
                DynTowerSpec::Rat(rc) => {
                    lemma_dts_mul_preserves_same_radicand_left(
                        *re_a, *re_b, DynTowerSpec::Rat(rc));
                    lemma_dts_mul_preserves_same_radicand_left(
                        *im_a, *im_b, DynTowerSpec::Rat(rc));
                },
                DynTowerSpec::Ext(re_c, im_c, _) => {
                    // re sub-terms:
                    lemma_dts_mul_preserves_same_radicand_left(*re_a, *re_b, *re_c);
                    lemma_dts_mul_preserves_same_radicand_left(*im_a, *im_b, *im_c);
                    lemma_dts_mul_preserves_same_radicand_right(
                        dts_mul(*im_a, *im_c), dts_mul(*im_b, *im_c), *d_a);
                    lemma_dts_add_preserves_same_radicand_both(
                        dts_mul(*re_a, *re_c), dts_mul(*re_b, *re_c),
                        dts_mul(*d_a, dts_mul(*im_a, *im_c)),
                        dts_mul(*d_a, dts_mul(*im_b, *im_c)));
                    // im sub-terms:
                    lemma_dts_mul_preserves_same_radicand_left(*re_a, *re_b, *im_c);
                    lemma_dts_mul_preserves_same_radicand_left(*im_a, *im_b, *re_c);
                    lemma_dts_add_preserves_same_radicand_both(
                        dts_mul(*re_a, *im_c), dts_mul(*re_b, *im_c),
                        dts_mul(*im_a, *re_c), dts_mul(*im_b, *re_c));
                },
            }
        },
        _ => {},
    }
}

/// If both are zero, their add is zero.
proof fn lemma_dts_add_both_zero(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_is_zero(a), dts_is_zero(b),
    ensures dts_is_zero(dts_add(a, b)),
{
    lemma_dts_is_zero_implies_eqv_zero(b);
    lemma_dts_add_is_zero_left(a, b);
    lemma_dts_eqv_transitive(dts_add(a, b), b, dts_zero());
    lemma_dts_eqv_zero_implies_is_zero(dts_add(a, b));
}

/// If x is zero, then add(y, x) ≡ y.
proof fn lemma_dts_add_is_zero_right(y: DynTowerSpec, x: DynTowerSpec)
    requires dts_is_zero(x),
    ensures dts_eqv(dts_add(y, x), y),
{
    lemma_dts_add_commutative(y, x);
    lemma_dts_add_is_zero_left(x, y);
    lemma_dts_eqv_transitive(dts_add(y, x), dts_add(x, y), y);
}

/// Add congruence (right): if eqv(a, b) then eqv(add(c, a), add(c, b)).
pub proof fn lemma_dts_add_congruence_right(c: DynTowerSpec, a: DynTowerSpec, b: DynTowerSpec)
    requires dts_eqv(a, b),
    ensures dts_eqv(dts_add(c, a), dts_add(c, b)),
{
    // add(c, a) ≡ add(a, c) by commutativity
    lemma_dts_add_commutative(c, a);
    // add(a, c) ≡ add(b, c) by congruence_left
    lemma_dts_add_congruence_left(a, b, c);
    // add(b, c) ≡ add(c, b) by commutativity
    lemma_dts_add_commutative(b, c);
    // Chain: add(c,a) ≡ add(a,c) ≡ add(b,c) ≡ add(c,b)
    lemma_dts_eqv_transitive(dts_add(c, a), dts_add(a, c), dts_add(b, c));
    lemma_dts_eqv_transitive(dts_add(c, a), dts_add(b, c), dts_add(c, b));
}

pub proof fn lemma_dts_add_inverse_right(a: DynTowerSpec)
    ensures dts_eqv(dts_add(a, dts_neg(a)), dts_zero()),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            Rational::axiom_add_inverse_right(r);
        },
        DynTowerSpec::Ext(re, im, _) => {
            // add(Ext(re,im,d), Ext(neg(re),neg(im),d))
            //   = Ext(add(re,neg(re)), add(im,neg(im)), d)
            // Need eqv(Ext(...), Rat(0))
            //   = eqv(add(re,neg(re)), Rat(0)) && is_zero(add(im,neg(im)))
            lemma_dts_add_inverse_right(*re);
            lemma_dts_add_inverse_right(*im);
            lemma_dts_eqv_zero_implies_is_zero(dts_add(*im, dts_neg(*im)));
        },
    }
}

pub proof fn lemma_dts_sub_is_add_neg(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(dts_sub(a, b), dts_add(a, dts_neg(b))),
{
    // dts_sub(a, b) = dts_add(a, dts_neg(b)) by definition
    lemma_dts_eqv_reflexive(dts_sub(a, b));
}

// ═══════════════════════════════════════════════════════════════════
//  Ring lemmas (radicand-independent)
// ═══════════════════════════════════════════════════════════════════

/// mul(a, one()) ≡ a.
pub proof fn lemma_dts_mul_one_right(a: DynTowerSpec)
    ensures dts_eqv(dts_mul(a, dts_one()), a),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            // mul(Rat(r), Rat(1)) = Rat(r * 1)
            Rational::axiom_mul_one_right(r);
        },
        DynTowerSpec::Ext(re, im, _) => {
            // mul(Ext(re,im,d), Rat(1)) = Ext(mul(*re, Rat(1)), mul(*im, Rat(1)), d)
            // Need: eqv(mul(*re,Rat(1)), *re) && eqv(mul(*im,Rat(1)), *im)
            lemma_dts_mul_one_right(*re);
            lemma_dts_mul_one_right(*im);
        },
    }
}

/// mul(a, zero()) ≡ zero().
pub proof fn lemma_dts_mul_zero_right(a: DynTowerSpec)
    ensures dts_eqv(dts_mul(a, dts_zero()), dts_zero()),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(r) => {
            // mul(Rat(r), Rat(0)) = Rat(r * 0)
            Rational::axiom_mul_zero_right(r);
        },
        DynTowerSpec::Ext(re, im, _) => {
            // mul(Ext(re,im,d), Rat(0)) = Ext(mul(*re, Rat(0)), mul(*im, Rat(0)), d)
            // Need: eqv(Ext(mul(*re,R0), mul(*im,R0), d), Rat(0))
            //      = eqv(mul(*re,R0), Rat(0)) && is_zero(mul(*im,R0))
            lemma_dts_mul_zero_right(*re);
            // eqv(mul(*re, Rat(0)), Rat(0)) ✓
            lemma_dts_mul_zero_right(*im);
            // eqv(mul(*im, Rat(0)), Rat(0)) → is_zero(mul(*im, Rat(0)))
            lemma_dts_eqv_zero_implies_is_zero(dts_mul(*im, dts_zero()));
        },
    }
}

/// one() ≢ zero().
pub proof fn lemma_dts_one_ne_zero()
    ensures !dts_eqv(dts_one(), dts_zero()),
{
    // dts_one() = Rat(from_int_spec(1)), dts_zero() = Rat(from_int_spec(0))
    // dts_eqv(Rat(1), Rat(0)) = from_int_spec(1).eqv(from_int_spec(0))
    Rational::axiom_one_ne_zero();
}

// ═══════════════════════════════════════════════════════════════════
//  Field lemma (definitional)
// ═══════════════════════════════════════════════════════════════════

/// div(a, b) ≡ mul(a, recip(b)).
pub proof fn lemma_dts_div_is_mul_recip(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(dts_div(a, b), dts_mul(a, dts_recip(b))),
{
    // dts_div(a, b) = dts_mul(a, dts_recip(b)) by definition
    lemma_dts_eqv_reflexive(dts_div(a, b));
}

// ═══════════════════════════════════════════════════════════════════
//  Ordering lemmas
// ═══════════════════════════════════════════════════════════════════

/// Helper: if dts_eqv(x, zero()), then dts_nonneg_fuel(x, fuel) for sufficient fuel.
///
/// Base case: 0 ≤ r follows from r ≡ 0 via le_congruence.
/// Inductive case: both re and im are zero-equivalent, so (a_nn && b_nn) holds.
pub proof fn lemma_dts_nonneg_fuel_zero(x: DynTowerSpec, fuel: nat)
    requires
        dts_eqv(x, dts_zero()),
        fuel >= dts_depth(x) + 1,
    ensures dts_nonneg_fuel(x, fuel),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(r) => {
            // nonneg_fuel(Rat(r), fuel) = 0.le_spec(r)
            // r ≡ 0, so 0 ≡ r by symmetry, and 0 ≤ 0 by reflexivity, so 0 ≤ r by congruence
            let zero = Rational::from_int_spec(0);
            Rational::axiom_le_reflexive(zero);
            Rational::axiom_eqv_reflexive(zero);
            Rational::axiom_eqv_symmetric(r, zero);
            Rational::axiom_le_congruence(zero, zero, zero, r);
        },
        DynTowerSpec::Ext(re, im, d) => {
            // eqv(Ext(re,im,d), Rat(0)) = eqv(*re, Rat(0)) && is_zero(*im)
            // nonneg_fuel needs fuel > 0: depth(Ext) >= 1, so fuel >= 2 > 0 ✓
            let f = (fuel - 1) as nat;
            // For *re: eqv(*re, Rat(0)), depth(*re) < depth(x), f >= depth(*re) + 1
            assert(f >= dts_depth(*re) + 1) by {
                // depth(x) = 1 + max(depth(*re), depth(*im), depth(*d))
                // f = fuel - 1 >= depth(x) = 1 + max(...) >= 1 + depth(*re)
            }
            lemma_dts_nonneg_fuel_zero(*re, f);
            // For *im: is_zero(*im) → eqv(*im, Rat(0))
            lemma_dts_is_zero_implies_eqv_zero(*im);
            assert(f >= dts_depth(*im) + 1) by {
                // same reasoning: f >= 1 + depth(*im)
            }
            lemma_dts_nonneg_fuel_zero(*im, f);
            // Now nonneg_fuel(*re, f) && nonneg_fuel(*im, f) → first disjunct true
        },
    }
}

/// If x is zero-equivalent, then x is nonneg.
pub proof fn lemma_dts_nonneg_zero(x: DynTowerSpec)
    requires dts_eqv(x, dts_zero()),
    ensures dts_nonneg(x),
{
    // dts_nonneg(x) = dts_nonneg_fuel(x, dts_depth(x) + 1)
    lemma_dts_nonneg_fuel_zero(x, dts_depth(x) + 1);
}

/// le(a, a) — reflexivity of ordering.
///
/// Proof: sub(a, a) = add(a, neg(a)) ≡ zero() (by add_inverse_right),
/// and zero-equivalent values are nonneg.
pub proof fn lemma_dts_le_reflexive(a: DynTowerSpec)
    ensures dts_le(a, a),
{
    // dts_le(a, a) = dts_nonneg(dts_sub(a, a))
    // dts_sub(a, a) = dts_add(a, dts_neg(a))
    lemma_dts_add_inverse_right(a);
    // dts_eqv(dts_add(a, dts_neg(a)), dts_zero())
    // = dts_eqv(dts_sub(a, a), dts_zero())
    lemma_dts_nonneg_zero(dts_sub(a, a));
    // dts_nonneg(dts_sub(a, a)) = dts_le(a, a)
}

/// lt(a, b) ⟺ le(a, b) ∧ ¬eqv(a, b) — definitional.
pub proof fn lemma_dts_lt_iff(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_lt(a, b) == (dts_le(a, b) && !dts_eqv(a, b)),
{
    // dts_lt(a, b) is defined as dts_le(a, b) && !dts_eqv(a, b)
    // Nothing to prove — definitional unfolding.
}

// ===========================================================================
//  Ordered field infrastructure for DynTowerSpec
// ===========================================================================

/// same_radicand is symmetric.
pub proof fn lemma_dts_same_radicand_symmetric(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_same_radicand(a, b),
    ensures dts_same_radicand(b, a),
    decreases a,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_same_radicand_symmetric(*re1, *re2);
            lemma_dts_same_radicand_symmetric(*im1, *im2);
        }
        _ => {}
    }
}

/// same_radicand is transitive.
pub proof fn lemma_dts_same_radicand_transitive(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires dts_same_radicand(a, b), dts_same_radicand(b, c),
    ensures dts_same_radicand(a, c),
    decreases a,
{
    match (a, b, c) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _),
         DynTowerSpec::Ext(re3, im3, _)) => {
            lemma_dts_same_radicand_transitive(*re1, *re2, *re3);
            lemma_dts_same_radicand_transitive(*im1, *im2, *im3);
        }
        _ => {} // cross-depth: same_radicand is false, requires is false
    }
}

/// same_radicand is reflexive.
pub proof fn lemma_dts_same_radicand_reflexive(a: DynTowerSpec)
    ensures dts_same_radicand(a, a),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(_) => {}
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_same_radicand_reflexive(*re);
            lemma_dts_same_radicand_reflexive(*im);
        }
    }
}

/// same_radicand(a, neg(a)) — negation preserves radicand structure.
pub proof fn lemma_dts_same_radicand_neg(a: DynTowerSpec)
    ensures dts_same_radicand(a, dts_neg(a)),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(_) => {}
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_same_radicand_neg(*re);
            lemma_dts_same_radicand_neg(*im);
        }
    }
}

/// neg preserves same_radicand structure.
pub proof fn lemma_dts_neg_preserves_same_radicand(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_same_radicand(a, b),
    ensures dts_same_radicand(dts_neg(a), dts_neg(b)),
    decreases a,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_neg_preserves_same_radicand(*re1, *re2);
            lemma_dts_neg_preserves_same_radicand(*im1, *im2);
        }
        _ => {}
    }
}

/// Depth of neg(x) equals depth of x.
pub proof fn lemma_dts_depth_neg(x: DynTowerSpec)
    ensures dts_depth(dts_neg(x)) == dts_depth(x),
    decreases x,
{
    match x {
        DynTowerSpec::Rat(_) => {}
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_depth_neg(*re);
            lemma_dts_depth_neg(*im);
        }
    }
}

/// Depth of mul(a, b) ≤ max(depth(a), depth(b)).
pub proof fn lemma_dts_depth_mul_le(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_depth(dts_mul(a, b)) <= if dts_depth(a) >= dts_depth(b)
        { dts_depth(a) } else { dts_depth(b) },
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Ext(re2, im2, _)) => {
            // mul(Ext, Ext) = Ext(add(mul(re,re2), mul(d,mul(im,im2))),
            //                     add(mul(re,im2), mul(im,re2)), d)
            lemma_dts_depth_mul_le(*re, *re2);
            lemma_dts_depth_mul_le(*im, *im2);
            lemma_dts_depth_mul_le(*re, *im2);
            lemma_dts_depth_mul_le(*im, *re2);
            lemma_dts_depth_mul_le(*d, dts_mul(*im, *im2));
            lemma_dts_depth_add_le(dts_mul(*re, *re2), dts_mul(*d, dts_mul(*im, *im2)));
            lemma_dts_depth_add_le(dts_mul(*re, *im2), dts_mul(*im, *re2));
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_depth_mul_le(DynTowerSpec::Rat(r), *re);
            lemma_dts_depth_mul_le(DynTowerSpec::Rat(r), *im);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_depth_mul_le(*re, DynTowerSpec::Rat(r));
            lemma_dts_depth_mul_le(*im, DynTowerSpec::Rat(r));
        }
    }
}

/// Depth of add(a, b) ≤ max(depth(a), depth(b)).
pub proof fn lemma_dts_depth_add_le(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_depth(dts_add(a, b)) <= if dts_depth(a) >= dts_depth(b)
        { dts_depth(a) } else { dts_depth(b) },
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_depth_add_le(*re1, *re2);
            lemma_dts_depth_add_le(*im1, *im2);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_depth_add_le(DynTowerSpec::Rat(r), *re);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_depth_add_le(*re, DynTowerSpec::Rat(r));
        }
    }
}

/// Fuel monotonicity: nonneg_fuel(x, f1) ∧ f1 ≤ f2 ⟹ nonneg_fuel(x, f2).
/// More fuel never breaks a nonneg result.
pub proof fn lemma_dts_nonneg_fuel_monotone(x: DynTowerSpec, f1: nat, f2: nat)
    requires dts_nonneg_fuel(x, f1), f1 <= f2,
    ensures dts_nonneg_fuel(x, f2),
    decreases f1,
{
    match x {
        DynTowerSpec::Rat(_) => {
            // nonneg_fuel(Rat(r), _) = 0.le(r), independent of fuel
        }
        DynTowerSpec::Ext(re, im, d) => {
            if f1 == 0 {
                // nonneg_fuel(Ext, 0) = false, requires is false
            } else {
                // f1 > 0 and f1 ≤ f2, so f2 > 0
                assert(f2 > 0);
                let sf1 = (f1 - 1) as nat;
                let sf2 = (f2 - 1) as nat;
                // The 3 cases at fuel f1 use sub-fuel sf1.
                // By IH, each sub-term transfers from sf1 to sf2.
                let a = *re; let b = *im; let dd = *d;
                let a_nn_1 = dts_nonneg_fuel(a, sf1);
                let b_nn_1 = dts_nonneg_fuel(b, sf1);
                let b_neg_1 = dts_nonneg_fuel(dts_neg(b), sf1) && !dts_is_zero(b);
                let b_pos_1 = b_nn_1 && !dts_is_zero(b);
                let a_neg_1 = dts_nonneg_fuel(dts_neg(a), sf1) && !dts_is_zero(a);

                if a_nn_1 && b_nn_1 {
                    // Case 1: transfer nonneg of re and im
                    lemma_dts_nonneg_fuel_monotone(a, sf1, sf2);
                    lemma_dts_nonneg_fuel_monotone(b, sf1, sf2);
                } else if a_nn_1 && b_neg_1 {
                    // Case 2: transfer nonneg(a), nonneg(neg(b)), and b²d ≤ a²
                    lemma_dts_nonneg_fuel_monotone(a, sf1, sf2);
                    lemma_dts_nonneg_fuel_monotone(dts_neg(b), sf1, sf2);
                    // b²d ≤ a² = nonneg_fuel(sub(a², d*b²), sf1)
                    lemma_dts_nonneg_fuel_monotone(
                        dts_sub(dts_mul(a, a), dts_mul(dd, dts_mul(b, b))), sf1, sf2);
                } else {
                    // Case 3: transfer nonneg(neg(a)), nonneg(b), and a² ≤ b²d
                    lemma_dts_nonneg_fuel_monotone(dts_neg(a), sf1, sf2);
                    lemma_dts_nonneg_fuel_monotone(b, sf1, sf2);
                    lemma_dts_nonneg_fuel_monotone(
                        dts_sub(dts_mul(dd, dts_mul(b, b)), dts_mul(a, a)), sf1, sf2);
                }
            }
        }
    }
}

/// nonneg_fuel transfers through component-wise eqv.
/// Induction on fuel: at fuel 0, Ext case is vacuously true.
/// At fuel f+1, use IH at fuel f for sub-field congruences.
pub proof fn lemma_dts_nonneg_fuel_congruence(
    x: DynTowerSpec, y: DynTowerSpec, fuel: nat,
)
    requires dts_eqv(x, y), dts_same_radicand(x, y), dts_nonneg_fuel(x, fuel),
    ensures dts_nonneg_fuel(y, fuel),
    decreases fuel,
{
    match (x, y) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            use verus_rational::rational::Rational;
            Rational::axiom_eqv_reflexive(Rational::from_int_spec(0));
            Rational::axiom_le_congruence(
                Rational::from_int_spec(0), Rational::from_int_spec(0), r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, _)) => {
            if fuel == 0 {
                // nonneg_fuel(Ext, 0) = false — requires is false
            } else {
                let f = (fuel - 1) as nat;
                let a1 = *re1; let b1 = *im1; let dd = *d1;
                let a2 = *re2; let b2 = *im2;

                // Squared term congruences: a1² ≡ a2², b1² ≡ b2², d*b1² ≡ d*b2²
                // Chain: a1*a1 ≡ a1*a2 (right varies) ≡ a2*a2 (left varies)
                lemma_dts_mul_congruence_right(a1, a2, a1);  // a1*a1 ≡ a1*a2
                lemma_dts_mul_congruence_left(a1, a2, a2);   // a1*a2 ≡ a2*a2
                lemma_dts_eqv_transitive(dts_mul(a1, a1), dts_mul(a1, a2), dts_mul(a2, a2));
                // b1² ≡ b2²
                lemma_dts_mul_congruence_right(b1, b2, b1);
                lemma_dts_mul_congruence_left(b1, b2, b2);
                lemma_dts_eqv_transitive(dts_mul(b1, b1), dts_mul(b1, b2), dts_mul(b2, b2));
                // same_radicand(b1*b1, b2*b2) via transitivity
                // mul_right(a, b, c): same_rad(a, b) ⟹ same_rad(c*a, c*b)
                // mul_left(a, b, c): same_rad(a, b) ⟹ same_rad(a*c, b*c)
                lemma_dts_mul_preserves_same_radicand_right(b1, b2, b1); // same_rad(b1*b1, b1*b2)
                lemma_dts_mul_preserves_same_radicand_left(b1, b2, b2);  // same_rad(b1*b2, b2*b2)
                lemma_dts_same_radicand_transitive(
                    dts_mul(b1, b1), dts_mul(b1, b2), dts_mul(b2, b2));
                // same_radicand(a1*a1, a2*a2)
                lemma_dts_mul_preserves_same_radicand_right(a1, a2, a1);
                lemma_dts_mul_preserves_same_radicand_left(a1, a2, a2);
                lemma_dts_same_radicand_transitive(
                    dts_mul(a1, a1), dts_mul(a1, a2), dts_mul(a2, a2));
                // d*b1² ≡ d*b2² and same_radicand
                lemma_dts_mul_preserves_same_radicand_right(dts_mul(b1, b1), dts_mul(b2, b2), dd);
                lemma_dts_mul_congruence_right(dts_mul(b1, b1), dts_mul(b2, b2), dd);

                // sub(a1², d*b1²) ≡ sub(a2², d*b2²) via add congruence chain
                let neg_db1 = dts_neg(dts_mul(dd, dts_mul(b1, b1)));
                let neg_db2 = dts_neg(dts_mul(dd, dts_mul(b2, b2)));
                lemma_dts_neg_congruence(dts_mul(dd, dts_mul(b1, b1)), dts_mul(dd, dts_mul(b2, b2)));
                lemma_dts_add_congruence_left(dts_mul(a1, a1), dts_mul(a2, a2), neg_db1);
                lemma_dts_add_congruence_right(dts_mul(a2, a2), neg_db1, neg_db2);
                // Chain: add(a1², neg_db1) ≡ add(a2², neg_db1) ≡ add(a2², neg_db2)
                lemma_dts_eqv_transitive(
                    dts_add(dts_mul(a1, a1), neg_db1),
                    dts_add(dts_mul(a2, a2), neg_db1),
                    dts_add(dts_mul(a2, a2), neg_db2));
                // Bridge: sub ≡ add(_, neg(_))
                lemma_dts_sub_is_add_neg(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1)));
                lemma_dts_sub_is_add_neg(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2)));
                // Full chain: sub1 ≡ add1 ≡ add2 ≡ sub2
                lemma_dts_eqv_transitive(
                    dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1))),
                    dts_add(dts_mul(a1, a1), neg_db1),
                    dts_add(dts_mul(a2, a2), neg_db2));
                lemma_dts_eqv_symmetric(
                    dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2))),
                    dts_add(dts_mul(a2, a2), neg_db2));
                lemma_dts_eqv_transitive(
                    dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1))),
                    dts_add(dts_mul(a2, a2), neg_db2),
                    dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2))));

                // sub(d*b1², a1²) ≡ sub(d*b2², a2²) — same pattern, swapped
                let neg_a1 = dts_neg(dts_mul(a1, a1));
                let neg_a2 = dts_neg(dts_mul(a2, a2));
                lemma_dts_neg_congruence(dts_mul(a1, a1), dts_mul(a2, a2));
                lemma_dts_add_congruence_left(dts_mul(dd, dts_mul(b1, b1)),
                    dts_mul(dd, dts_mul(b2, b2)), neg_a1);
                lemma_dts_add_congruence_right(dts_mul(dd, dts_mul(b2, b2)), neg_a1, neg_a2);
                lemma_dts_eqv_transitive(
                    dts_add(dts_mul(dd, dts_mul(b1, b1)), neg_a1),
                    dts_add(dts_mul(dd, dts_mul(b2, b2)), neg_a1),
                    dts_add(dts_mul(dd, dts_mul(b2, b2)), neg_a2));
                lemma_dts_sub_is_add_neg(dts_mul(dd, dts_mul(b1, b1)), dts_mul(a1, a1));
                lemma_dts_sub_is_add_neg(dts_mul(dd, dts_mul(b2, b2)), dts_mul(a2, a2));
                lemma_dts_eqv_transitive(
                    dts_sub(dts_mul(dd, dts_mul(b1, b1)), dts_mul(a1, a1)),
                    dts_add(dts_mul(dd, dts_mul(b1, b1)), neg_a1),
                    dts_add(dts_mul(dd, dts_mul(b2, b2)), neg_a2));
                lemma_dts_eqv_symmetric(
                    dts_sub(dts_mul(dd, dts_mul(b2, b2)), dts_mul(a2, a2)),
                    dts_add(dts_mul(dd, dts_mul(b2, b2)), neg_a2));
                lemma_dts_eqv_transitive(
                    dts_sub(dts_mul(dd, dts_mul(b1, b1)), dts_mul(a1, a1)),
                    dts_add(dts_mul(dd, dts_mul(b2, b2)), neg_a2),
                    dts_sub(dts_mul(dd, dts_mul(b2, b2)), dts_mul(a2, a2)));

                // Now dispatch on which case x satisfies
                let a1_nn = dts_nonneg_fuel(a1, f);
                let b1_nn = dts_nonneg_fuel(b1, f);

                // same_radicand for neg terms
                lemma_dts_neg_preserves_same_radicand(a1, a2);
                lemma_dts_neg_preserves_same_radicand(b1, b2);
                // same_radicand for compound sub terms
                lemma_dts_neg_preserves_same_radicand(
                    dts_mul(dd, dts_mul(b1, b1)), dts_mul(dd, dts_mul(b2, b2)));
                lemma_dts_add_preserves_same_radicand_both(
                    dts_mul(a1, a1), dts_mul(a2, a2),
                    dts_neg(dts_mul(dd, dts_mul(b1, b1))),
                    dts_neg(dts_mul(dd, dts_mul(b2, b2))));
                lemma_dts_neg_preserves_same_radicand(
                    dts_mul(a1, a1), dts_mul(a2, a2));
                lemma_dts_add_preserves_same_radicand_both(
                    dts_mul(dd, dts_mul(b1, b1)), dts_mul(dd, dts_mul(b2, b2)),
                    dts_neg(dts_mul(a1, a1)), dts_neg(dts_mul(a2, a2)));

                if a1_nn && b1_nn {
                    // Case 1 → Case 1
                    lemma_dts_nonneg_fuel_congruence(a1, a2, f);
                    lemma_dts_nonneg_fuel_congruence(b1, b2, f);
                } else if a1_nn && dts_nonneg_fuel(dts_neg(b1), f) && !dts_is_zero(b1) {
                    // Case 2 → Case 2
                    lemma_dts_nonneg_fuel_congruence(a1, a2, f);
                    // Establish neg preconditions locally
                    lemma_dts_neg_congruence(b1, b2);
                    lemma_dts_neg_preserves_same_radicand(b1, b2);
                    lemma_dts_nonneg_fuel_congruence(dts_neg(b1), dts_neg(b2), f);
                    if dts_is_zero(b2) {
                        lemma_dts_eqv_symmetric(b1, b2);
                        lemma_dts_is_zero_congruence(b2, b1);
                    }
                    lemma_dts_nonneg_fuel_congruence(
                        dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1))),
                        dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2))), f);
                } else {
                    // Case 3 → Case 3
                    lemma_dts_neg_congruence(a1, a2);
                    lemma_dts_neg_preserves_same_radicand(a1, a2);
                    lemma_dts_nonneg_fuel_congruence(dts_neg(a1), dts_neg(a2), f);
                    if dts_is_zero(a2) {
                        lemma_dts_eqv_symmetric(a1, a2);
                        lemma_dts_is_zero_congruence(a2, a1);
                    }
                    lemma_dts_nonneg_fuel_congruence(b1, b2, f);
                    if dts_is_zero(b2) {
                        lemma_dts_eqv_symmetric(b1, b2);
                        lemma_dts_is_zero_congruence(b2, b1);
                    }
                    lemma_dts_nonneg_fuel_congruence(
                        dts_sub(dts_mul(dd, dts_mul(b1, b1)), dts_mul(a1, a1)),
                        dts_sub(dts_mul(dd, dts_mul(b2, b2)), dts_mul(a2, a2)), f);
                }
            }
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            if fuel == 0 {
            } else {
                let f = (fuel - 1) as nat;
                // eqv(Rat(r), Ext(re, im, d)) means eqv(Rat(r), re) && is_zero(im)
                lemma_dts_eqv_symmetric(DynTowerSpec::Rat(r), *re);
                // nonneg(Rat(r)) at any fuel. Transfer to re at fuel f.
                lemma_dts_nonneg_fuel_congruence(DynTowerSpec::Rat(r), *re, f);
                // is_zero(im) → nonneg(im) at fuel f
                lemma_dts_nonneg_fuel_zero(*im, f);
                // Case 1: nonneg(re) && nonneg(im)
            }
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            if fuel == 0 {
            } else {
                let f = (fuel - 1) as nat;
                // eqv(Ext(re, im, d), Rat(r)) means eqv(re, Rat(r)) && is_zero(im)
                let a1 = *re; let b1 = *im;

                if dts_nonneg_fuel(a1, f) {
                    // re ≥ 0, re ≡ Rat(r) → Rat(r) ≥ 0
                    lemma_dts_nonneg_fuel_congruence(a1, DynTowerSpec::Rat(r), f);
                } else {
                    // Case 3: neg(re) && pos(im). But is_zero(im) contradicts pos(im).
                    // pos = nonneg && !is_zero. is_zero(im) from eqv. Contradiction.
                }
            }
        }
    }
}

/// Fuel stabilization: for sufficient fuel (≥ depth+1), nonneg_fuel agrees with nonneg.
/// Uses decreases f since compound sub-terms (neg, mul, sub) aren't structurally smaller.
pub proof fn lemma_dts_nonneg_fuel_stabilize(x: DynTowerSpec, f: nat)
    requires f >= dts_depth(x) + 1,
    ensures dts_nonneg_fuel(x, f) == dts_nonneg(x),
    decreases f,
{
    match x {
        DynTowerSpec::Rat(_) => {
            // fuel-independent for Rat
        }
        DynTowerSpec::Ext(re, im, d) => {
            let sf = (f - 1) as nat;
            let sd = dts_depth(x) as nat; // canonical sub-fuel for nonneg(x)
            // Both sf and sd >= depth of each sub-term + 1
            // (depth(x) = 1 + max(depth(re), depth(im), depth(d)))
            // IH on direct sub-terms at both fuel levels
            lemma_dts_nonneg_fuel_stabilize(*re, sf);
            lemma_dts_nonneg_fuel_stabilize(*im, sf);
            lemma_dts_nonneg_fuel_stabilize(*re, sd);
            lemma_dts_nonneg_fuel_stabilize(*im, sd);
            // neg preserves depth
            lemma_dts_depth_neg(*re);
            lemma_dts_depth_neg(*im);
            lemma_dts_nonneg_fuel_stabilize(dts_neg(*re), sf);
            lemma_dts_nonneg_fuel_stabilize(dts_neg(*im), sf);
            lemma_dts_nonneg_fuel_stabilize(dts_neg(*re), sd);
            lemma_dts_nonneg_fuel_stabilize(dts_neg(*im), sd);
            // Compound terms: depth(mul/add/sub/neg) ≤ max sub-depths
            let a2 = dts_mul(*re, *re);
            let b2 = dts_mul(*im, *im);
            let b2d = dts_mul(*d, b2);
            lemma_dts_depth_mul_le(*re, *re);
            lemma_dts_depth_mul_le(*im, *im);
            lemma_dts_depth_mul_le(*d, b2);
            lemma_dts_depth_neg(a2);
            lemma_dts_depth_neg(b2d);
            lemma_dts_depth_add_le(a2, dts_neg(b2d));
            lemma_dts_depth_add_le(b2d, dts_neg(a2));
            lemma_dts_nonneg_fuel_stabilize(dts_sub(a2, b2d), sf);
            lemma_dts_nonneg_fuel_stabilize(dts_sub(b2d, a2), sf);
            lemma_dts_nonneg_fuel_stabilize(dts_sub(a2, b2d), sd);
            lemma_dts_nonneg_fuel_stabilize(dts_sub(b2d, a2), sd);
            // All sub-term nonneg_fuel values agree between sf and sd.
            // Z3 sees both fuel levels produce the same 3-case booleans.
        }
    }
}

/// nonneg transfers through eqv (requires same radicand structure).
pub proof fn lemma_dts_nonneg_congruence(
    x: DynTowerSpec, y: DynTowerSpec,
)
    requires dts_eqv(x, y), dts_same_radicand(x, y), dts_nonneg(x),
    ensures dts_nonneg(y),
{
    let fx = dts_depth(x) + 1;
    let fy = dts_depth(y) + 1;
    let fuel = if fx >= fy { fx } else { fy };
    // Upward-transfer x's nonneg to common fuel
    lemma_dts_nonneg_fuel_monotone(x, fx, fuel);
    // Transfer through eqv at common fuel
    lemma_dts_nonneg_fuel_congruence(x, y, fuel);
    // Stabilize: nonneg_fuel(y, fuel) == nonneg(y) since fuel >= fy
    lemma_dts_nonneg_fuel_stabilize(y, fuel);
}

/// Total ordering: every DynTowerSpec value is nonneg or its negation is.
/// Requires sufficient fuel (≥ depth+1) to fully evaluate nonneg.
#[verifier::rlimit(120)]
pub proof fn lemma_dts_nonneg_or_neg_nonneg_fuel(x: DynTowerSpec, fuel: nat)
    requires fuel >= dts_depth(x) + 1, dts_well_formed(x),
    ensures dts_nonneg_fuel(x, fuel) || dts_nonneg_fuel(dts_neg(x), fuel),
    decreases fuel,
{
    match x {
        DynTowerSpec::Rat(r) => {
            use verus_rational::rational::Rational;
            Rational::axiom_le_total(Rational::from_int_spec(0), r);
            if !Rational::from_int_spec(0).le_spec(r) {
                verus_algebra::lemmas::ordered_ring_lemmas::lemma_neg_nonpos_iff::<Rational>(r);
            }
        }
        DynTowerSpec::Ext(re, im, d) => {
            // fuel >= depth(x) + 1 >= 2, so fuel > 0
            let f = (fuel - 1) as nat;
            let a = *re; let b = *im; let dd = *d;
            let na = dts_neg(a); let nb = dts_neg(b);

            // Depth bounds for all sub-terms and compound terms
            lemma_dts_depth_neg(a); lemma_dts_depth_neg(b);
            lemma_dts_depth_mul_le(a, a); lemma_dts_depth_mul_le(b, b);
            lemma_dts_depth_mul_le(dd, dts_mul(b, b));
            lemma_dts_depth_mul_le(na, na); lemma_dts_depth_mul_le(nb, nb);
            lemma_dts_depth_mul_le(dd, dts_mul(nb, nb));
            lemma_dts_depth_neg(dts_mul(a, a)); lemma_dts_depth_neg(dts_mul(dd, dts_mul(b, b)));
            lemma_dts_depth_neg(dts_mul(na, na)); lemma_dts_depth_neg(dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_depth_add_le(dts_mul(a, a), dts_neg(dts_mul(dd, dts_mul(b, b))));
            lemma_dts_depth_add_le(dts_mul(dd, dts_mul(b, b)), dts_neg(dts_mul(a, a)));
            lemma_dts_depth_add_le(dts_mul(na, na), dts_neg(dts_mul(dd, dts_mul(nb, nb))));
            lemma_dts_depth_add_le(dts_mul(dd, dts_mul(nb, nb)), dts_neg(dts_mul(na, na)));

            // Recursive le_total on sub-components
            lemma_dts_nonneg_or_neg_nonneg_fuel(a, f);
            lemma_dts_nonneg_or_neg_nonneg_fuel(b, f);
            // well_formed for compound terms (mul, sub of sub-components)
            lemma_dts_same_radicand_reflexive(a);
            lemma_dts_mul_well_formed(a, a);
            lemma_dts_same_radicand_reflexive(b);
            lemma_dts_mul_well_formed(b, b);
            lemma_dts_same_radicand_symmetric(a, dd);
            lemma_dts_same_radicand_transitive(dd, a, b);
            lemma_dts_same_radicand_closed_mul(dd, b, b);
            lemma_dts_mul_well_formed(dd, dts_mul(b, b));
            // sub = add + neg
            lemma_dts_neg_well_formed(dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_closed_mul(a, a, a);
            lemma_dts_same_radicand_transitive(a, dd, dts_mul(b, b));
            lemma_dts_same_radicand_closed_mul(a, dd, dts_mul(b, b));
            lemma_dts_same_radicand_neg(dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_closed_add(a,
                dts_mul(a, a),
                dts_neg(dts_mul(dd, dts_mul(b, b))));
            lemma_dts_same_radicand_symmetric(a,
                dts_sub(dts_mul(a, a), dts_mul(dd, dts_mul(b, b))));
            lemma_dts_add_well_formed(
                dts_mul(a, a),
                dts_neg(dts_mul(dd, dts_mul(b, b))));
            // le_total on x's squared comparison
            lemma_dts_nonneg_or_neg_nonneg_fuel(
                dts_sub(dts_mul(a, a), dts_mul(dd, dts_mul(b, b))), f);
            // neg(x)'s compound terms similarly
            lemma_dts_neg_well_formed(a);
            lemma_dts_neg_well_formed(b);
            lemma_dts_same_radicand_reflexive(na);
            lemma_dts_mul_well_formed(na, na);
            lemma_dts_same_radicand_reflexive(nb);
            lemma_dts_mul_well_formed(nb, nb);
            lemma_dts_same_radicand_neg(a);
            lemma_dts_same_radicand_symmetric(a, na);
            lemma_dts_same_radicand_transitive(na, a, dd);
            lemma_dts_same_radicand_transitive(na, a, b);
            lemma_dts_same_radicand_neg(b);
            lemma_dts_same_radicand_symmetric(b, nb);
            lemma_dts_same_radicand_transitive(na, a, nb);
            lemma_dts_same_radicand_closed_mul(na, nb, nb);
            lemma_dts_mul_well_formed(dd, dts_mul(nb, nb));
            lemma_dts_neg_well_formed(dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_same_radicand_closed_mul(na, na, na);
            lemma_dts_same_radicand_transitive(na, na, dd);
            lemma_dts_same_radicand_closed_mul(na, dd, dts_mul(nb, nb));
            lemma_dts_same_radicand_neg(dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_same_radicand_closed_add(na,
                dts_mul(na, na),
                dts_neg(dts_mul(dd, dts_mul(nb, nb))));
            lemma_dts_add_well_formed(
                dts_mul(na, na),
                dts_neg(dts_mul(dd, dts_mul(nb, nb))));
            // le_total on neg(x)'s squared comparison
            lemma_dts_nonneg_or_neg_nonneg_fuel(
                dts_sub(dts_mul(na, na), dts_mul(dd, dts_mul(nb, nb))), f);

            // Zero/involution hints for is_zero and neg(neg(x))
            if dts_is_zero(a) {
                lemma_dts_is_zero_implies_eqv_zero(a);
                lemma_dts_nonneg_fuel_zero(a, f);
                lemma_dts_neg_preserves_is_zero(a);
                lemma_dts_is_zero_implies_eqv_zero(na);
                lemma_dts_nonneg_fuel_zero(na, f);
            }
            if dts_is_zero(b) {
                lemma_dts_is_zero_implies_eqv_zero(b);
                lemma_dts_nonneg_fuel_zero(b, f);
                lemma_dts_neg_preserves_is_zero(b);
                lemma_dts_is_zero_implies_eqv_zero(nb);
                lemma_dts_nonneg_fuel_zero(nb, f);
            }
            if dts_is_zero(na) {
                lemma_dts_is_zero_implies_eqv_zero(na);
                lemma_dts_nonneg_fuel_zero(na, f);
            }
            if dts_is_zero(nb) {
                lemma_dts_is_zero_implies_eqv_zero(nb);
                lemma_dts_nonneg_fuel_zero(nb, f);
            }

            // neg(neg(a)) ≡ a and neg(neg(b)) ≡ b for C3(neg) conditions
            lemma_dts_neg_involution(a);
            lemma_dts_neg_involution(b);
            // Transfer: nonneg(a, f) → nonneg(neg(neg(a)), f) and vice versa
            if dts_nonneg_fuel(a, f) {
                // nonneg(a) → nonneg(neg(neg(a))) by involution + congruence
                lemma_dts_eqv_symmetric(dts_neg(dts_neg(a)), a);
                lemma_dts_same_radicand_neg(a);
                lemma_dts_same_radicand_neg(na);
                lemma_dts_same_radicand_transitive(a, na, dts_neg(na));
                lemma_dts_eqv_symmetric(a, dts_neg(na));
                lemma_dts_nonneg_fuel_congruence(a, dts_neg(na), f);
            }
            if dts_nonneg_fuel(b, f) {
                lemma_dts_eqv_symmetric(dts_neg(dts_neg(b)), b);
                lemma_dts_same_radicand_neg(b);
                lemma_dts_same_radicand_neg(nb);
                lemma_dts_same_radicand_transitive(b, nb, dts_neg(nb));
                lemma_dts_eqv_symmetric(b, dts_neg(nb));
                lemma_dts_nonneg_fuel_congruence(b, dts_neg(nb), f);
            }

            // Provide ALL squared comparisons from le_total (both directions for x and neg(x))
            lemma_dts_nonneg_or_neg_nonneg_fuel(
                dts_sub(dts_mul(dd, dts_mul(b, b)), dts_mul(a, a)), f);
            lemma_dts_nonneg_or_neg_nonneg_fuel(
                dts_sub(dts_mul(dd, dts_mul(nb, nb)), dts_mul(na, na)), f);

            // neg_square: mul(neg(a), neg(a)) ≡ mul(a, a) — bridges x and neg(x) squared terms
            lemma_dts_neg_square(a);
            lemma_dts_neg_square(b);
            // same_radicand(neg(b)², b²) via neg + symmetric + mul chain
            lemma_dts_same_radicand_neg(b);
            lemma_dts_same_radicand_symmetric(b, nb);
            lemma_dts_mul_preserves_same_radicand_left(nb, b, nb);
            lemma_dts_mul_preserves_same_radicand_right(nb, b, b);
            lemma_dts_same_radicand_transitive(dts_mul(nb, nb), dts_mul(b, nb), dts_mul(b, b));
            // d * neg(b)² ≡ d * b²
            lemma_dts_mul_preserves_same_radicand_right(dts_mul(nb, nb), dts_mul(b, b), dd);
            lemma_dts_mul_congruence_left(dts_mul(nb, nb), dts_mul(b, b), dd);
            // same_radicand(neg(a)², a²)
            lemma_dts_neg_square(a);
            lemma_dts_same_radicand_neg(a);
            lemma_dts_same_radicand_symmetric(a, na);
            lemma_dts_mul_preserves_same_radicand_left(na, a, na);
            lemma_dts_mul_preserves_same_radicand_right(na, a, a);
            lemma_dts_same_radicand_transitive(dts_mul(na, na), dts_mul(a, na), dts_mul(a, a));

            // Explicit case dispatch with return-per-branch
            let a_nn = dts_nonneg_fuel(a, f);
            let b_nn = dts_nonneg_fuel(b, f);
            let na_nn = dts_nonneg_fuel(na, f);
            let nb_nn = dts_nonneg_fuel(nb, f);

            if a_nn && b_nn { return; }       // C1(x)
            if na_nn && nb_nn { return; }     // C1(neg(x))
        }
    }
}

} // verus!
