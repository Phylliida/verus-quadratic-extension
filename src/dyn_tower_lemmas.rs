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

/// Tower closure for add: produces same_radicand AND well_formed result.
#[verifier::rlimit(40)]
pub proof fn lemma_dts_add_closed(
    a: DynTowerSpec, b: DynTowerSpec,
)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures
        dts_well_formed(dts_add(a, b)),
        dts_same_radicand(a, dts_add(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_add_closed(*re1, *re2);
            lemma_dts_add_closed(*im1, *im2);
            // same_radicand(add(re1,re2), add(im1,im2))
            // same_radicand(re1, im1) from well_formed(a), same_radicand(re2, im2) from well_formed(b)
            lemma_dts_add_preserves_same_radicand_both(*re1, *im1, *re2, *im2);
            // same_radicand(add(re1,re2), d1) via chain: d1~re1~add(re1,re2)
            lemma_dts_same_radicand_symmetric(*re1, *d1);
            lemma_dts_same_radicand_transitive(*d1, *re1, *re2);
            // From IH: same_radicand(re1, add(re1, re2))
            lemma_dts_same_radicand_transitive(*d1, *re1, dts_add(*re1, *re2));
            lemma_dts_same_radicand_symmetric(*d1, dts_add(*re1, *re2));
            // Explicit assertions for Z3
            assert(dts_well_formed(dts_add(*re1, *re2)));
            assert(dts_well_formed(dts_add(*im1, *im2)));
            assert(dts_well_formed(*d1));
            assert(dts_same_radicand(dts_add(*re1, *re2), dts_add(*im1, *im2)));
            assert(dts_same_radicand(dts_add(*re1, *re2), *d1));
        }
        // Cross-depth: same_radicand(Rat, Ext) = false, requires is contradictory
        _ => {}
    }
}

/// Tower closure for mul: produces same_radicand AND well_formed result.
#[verifier::rlimit(40)]
pub proof fn lemma_dts_mul_closed(
    a: DynTowerSpec, b: DynTowerSpec,
)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures
        dts_well_formed(dts_mul(a, b)),
        dts_same_radicand(a, dts_mul(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            // Cross same_radicand between all sub-components
            lemma_dts_same_radicand_symmetric(*im1, *im2);
            lemma_dts_same_radicand_transitive(*re1, *im1, *im2);
            lemma_dts_same_radicand_symmetric(*re1, *im1);
            lemma_dts_same_radicand_transitive(*im1, *re1, *re2);
            lemma_dts_same_radicand_symmetric(*re1, *d);
            lemma_dts_same_radicand_transitive(*d, *re1, *im1);
            lemma_dts_same_radicand_transitive(*d, *im1, *im2);

            // 4 sub-products: well_formed + closed
            lemma_dts_mul_closed(*re1, *re2);
            lemma_dts_mul_closed(*im1, *im2);
            lemma_dts_mul_closed(*re1, *im2);
            lemma_dts_mul_closed(*im1, *re2);
            // d * im1*im2: same_radicand(d, mul(im1,im2)) by chain: d~im1~mul(im1,im2)
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_transitive(*d, *im1, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_symmetric(*d, dts_mul(*im1, *im2));
            lemma_dts_mul_closed(*d, dts_mul(*im1, *im2));
            // same_radicand for add_closed preconditions:
            // mul(re1,re2) ~ re1 [from mul_closed ensures, symmetric]
            // mul(d,mul(im1,im2)) ~ d [from mul_closed ensures, symmetric]
            // re1 ~ d [established above]
            // So mul(re1,re2) ~ re1 ~ d ~ mul(d,...) by transitivity
            lemma_dts_same_radicand_symmetric(*re1, dts_mul(*re1, *re2));
            lemma_dts_same_radicand_symmetric(*d, dts_mul(*d, dts_mul(*im1, *im2)));
            lemma_dts_same_radicand_transitive(
                dts_mul(*re1, *re2), *re1, *d);
            lemma_dts_same_radicand_transitive(
                dts_mul(*re1, *re2), *d, dts_mul(*d, dts_mul(*im1, *im2)));
            // re_product = add(re1*re2, d*im1*im2)
            lemma_dts_add_closed(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            // same_radicand for im add: mul(re1,im2) ~ re1, mul(im1,re2) ~ im1 ~ re1
            lemma_dts_same_radicand_symmetric(*re1, dts_mul(*re1, *im2));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *re2));
            lemma_dts_same_radicand_transitive(
                dts_mul(*re1, *im2), *re1, *im1);
            lemma_dts_same_radicand_transitive(
                dts_mul(*re1, *im2), *im1, dts_mul(*im1, *re2));
            // im_product = add(re1*im2, im1*re2)
            lemma_dts_add_closed(dts_mul(*re1, *im2), dts_mul(*im1, *re2));

            // For well_formed(result): need same_radicand(re_product, im_product) and same_radicand(re_product, d)
            let re_prod = dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            let im_prod = dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2));
            // re_prod ~ mul(re1,re2) ~ re1 (from add_closed + mul_closed ensures, symmetric + transitivity)
            lemma_dts_same_radicand_symmetric(dts_mul(*re1, *re2), re_prod);
            lemma_dts_same_radicand_transitive(re_prod, dts_mul(*re1, *re2), *re1);
            // im_prod ~ mul(re1,im2) ~ re1
            lemma_dts_same_radicand_symmetric(dts_mul(*re1, *im2), im_prod);
            lemma_dts_same_radicand_transitive(im_prod, dts_mul(*re1, *im2), *re1);
            // re_prod ~ re1 ~ d → re_prod ~ d
            lemma_dts_same_radicand_transitive(re_prod, *re1, *d);
            // re_prod ~ re1 ~ im_prod (symmetric chain)
            lemma_dts_same_radicand_symmetric(im_prod, *re1);
            lemma_dts_same_radicand_transitive(re_prod, *re1, im_prod);
            // Explicit assertions
            assert(dts_well_formed(re_prod));
            assert(dts_well_formed(im_prod));
            assert(dts_well_formed(*d));
            assert(dts_same_radicand(re_prod, im_prod));
            assert(dts_same_radicand(re_prod, *d));
            // For same_radicand(a, mul(a, b)): need re1~re_prod and im1~im_prod
            lemma_dts_same_radicand_symmetric(re_prod, *re1);
            lemma_dts_same_radicand_transitive(*im1, *re1, im_prod);
        }
        // Cross-depth: same_radicand(Rat, Ext) = false
        _ => {}
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


/// neg(sub(a, b)) ≡ sub(b, a) (negation swaps subtraction order).
pub proof fn lemma_dts_neg_sub_swap(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(dts_neg(dts_sub(a, b)), dts_sub(b, a)),
    decreases a, b,
{
    // neg(sub(a,b)) = neg(add(a, neg(b)))
    lemma_dts_sub_is_add_neg(a, b);
    lemma_dts_neg_congruence(dts_sub(a, b), dts_add(a, dts_neg(b)));
    // neg(add(a, neg(b))) ≡ add(neg(a), neg(neg(b))) by neg_add... but we don't have neg_add for DTS
    // Alternative: neg(add(a, neg(b))) ≡ add(neg(a), b) via:
    //   add(a, neg(b)) + add(neg(a), b) = (a + neg(a)) + (neg(b) + b) = 0 + 0 = 0
    //   So neg(add(a, neg(b))) ≡ add(neg(a), b) by uniqueness of additive inverse.
    // This needs add_inverse + add_commutative + add_associative.
    // Simpler: just use sub_is_add_neg on both sides and show structural eqv.
    // sub(b, a) = add(b, neg(a)). And neg(sub(a,b))... hard without neg_add.
    // Let me try: Z3 may unfold for small depth since all are open spec fn.
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            verus_algebra::lemmas::additive_group_lemmas::lemma_neg_sub::<
                verus_rational::rational::Rational>(r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, _), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_neg_sub_swap(*re1, *re2);
            lemma_dts_neg_sub_swap(*im1, *im2);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, _)) => {
            lemma_dts_neg_sub_swap(DynTowerSpec::Rat(r), *re);
            lemma_dts_neg_involution(*im);
        }
        (DynTowerSpec::Ext(re, im, _), DynTowerSpec::Rat(r)) => {
            lemma_dts_neg_sub_swap(*re, DynTowerSpec::Rat(r));
            lemma_dts_neg_involution(*im);
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

/// If eqv(a, c) and eqv(b, d) with same_radicand, then sub(a,b) ≡ sub(c,d) with same_radicand.
pub proof fn lemma_dts_sub_congruence_both(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec, d: DynTowerSpec,
)
    requires
        dts_eqv(a, c), dts_eqv(b, d),
        dts_same_radicand(a, c), dts_same_radicand(b, d),
    ensures
        dts_eqv(dts_sub(a, b), dts_sub(c, d)),
        dts_same_radicand(dts_sub(a, b), dts_sub(c, d)),
{
    lemma_dts_neg_congruence(b, d);
    lemma_dts_neg_preserves_same_radicand(b, d);
    lemma_dts_add_congruence_left(a, c, dts_neg(b));
    lemma_dts_add_congruence_right(c, dts_neg(b), dts_neg(d));
    lemma_dts_eqv_transitive(
        dts_add(a, dts_neg(b)), dts_add(c, dts_neg(b)), dts_add(c, dts_neg(d)));
    lemma_dts_add_preserves_same_radicand_both(a, c, dts_neg(b), dts_neg(d));
}

/// Total ordering: every DynTowerSpec value is nonneg or its negation is.
/// Requires sufficient fuel (≥ depth+1) to fully evaluate nonneg.
#[verifier::rlimit(200)]
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
            lemma_dts_mul_closed(a, a);
            lemma_dts_same_radicand_reflexive(b);
            lemma_dts_mul_closed(b, b);
            lemma_dts_same_radicand_symmetric(a, dd);
            lemma_dts_same_radicand_transitive(dd, a, b);
            lemma_dts_same_radicand_transitive(dd, b, dts_mul(b, b));
            lemma_dts_mul_closed(dd, dts_mul(b, b));
            lemma_dts_neg_well_formed(dts_mul(dd, dts_mul(b, b)));
            // same_radicand(mul(a,a), neg(mul(dd, mul(b,b)))) for add_closed
            lemma_dts_same_radicand_symmetric(a, dts_mul(a, a));
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_transitive(dts_mul(a, a), a, dd);
            lemma_dts_same_radicand_transitive(
                dts_mul(a, a), dd, dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_neg(dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_transitive(
                dts_mul(a, a), dts_mul(dd, dts_mul(b, b)),
                dts_neg(dts_mul(dd, dts_mul(b, b))));
            lemma_dts_add_closed(
                dts_mul(a, a),
                dts_neg(dts_mul(dd, dts_mul(b, b))));
            // le_total on x's squared comparison
            lemma_dts_nonneg_or_neg_nonneg_fuel(
                dts_sub(dts_mul(a, a), dts_mul(dd, dts_mul(b, b))), f);
            // neg(x)'s compound terms similarly
            lemma_dts_neg_well_formed(a);
            lemma_dts_neg_well_formed(b);
            lemma_dts_same_radicand_reflexive(na);
            lemma_dts_mul_closed(na, na);
            lemma_dts_same_radicand_reflexive(nb);
            lemma_dts_mul_closed(nb, nb);
            lemma_dts_same_radicand_neg(a);
            lemma_dts_same_radicand_symmetric(a, na);
            lemma_dts_same_radicand_transitive(na, a, dd);
            lemma_dts_same_radicand_transitive(na, a, b);
            lemma_dts_same_radicand_neg(b);
            lemma_dts_same_radicand_symmetric(b, nb);
            lemma_dts_same_radicand_transitive(a, b, nb);
            lemma_dts_same_radicand_transitive(na, a, nb);
            // same_radicand(dd, nb): dd~a~b~nb by chain
            lemma_dts_same_radicand_transitive(dd, a, b);
            lemma_dts_same_radicand_transitive(dd, b, nb);
            // same_radicand(dd, mul(nb,nb))
            lemma_dts_same_radicand_transitive(dd, nb, dts_mul(nb, nb));
            lemma_dts_mul_closed(dd, dts_mul(nb, nb));
            lemma_dts_neg_well_formed(dts_mul(dd, dts_mul(nb, nb)));
            // same_radicand for neg(x)'s add_closed
            lemma_dts_same_radicand_symmetric(na, dts_mul(na, na));
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_same_radicand_transitive(dts_mul(na, na), na, dd);
            lemma_dts_same_radicand_transitive(
                dts_mul(na, na), dd, dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_same_radicand_neg(dts_mul(dd, dts_mul(nb, nb)));
            lemma_dts_same_radicand_transitive(
                dts_mul(na, na), dts_mul(dd, dts_mul(nb, nb)),
                dts_neg(dts_mul(dd, dts_mul(nb, nb))));
            lemma_dts_add_closed(
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

            // Z3 has le_total for (a,b,na,nb) + squared comparisons for both x and neg(x).

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

            // Case dispatch: guided nested if-else for exhaustive coverage
            let a_nn = dts_nonneg_fuel(a, f);
            let b_nn = dts_nonneg_fuel(b, f);
            let na_nn = dts_nonneg_fuel(na, f);
            let nb_nn = dts_nonneg_fuel(nb, f);

            if a_nn && b_nn { return; }       // C1(x)
            if na_nn && nb_nn { return; }     // C1(neg(x))

            // After both C1 fail, two remaining cases:
            // Case A: a_nn && !b_nn (then nb_nn from IH, !na_nn from !C1_neg)
            // Case D: !a_nn && b_nn (then na_nn from IH, !nb_nn from !C1_neg)

            let sub_x = dts_sub(dts_mul(a, a), dts_mul(dd, dts_mul(b, b)));

            // Bridge: neg(sub_x) ≡ sub_x_rev → nonneg(sub_x) || nonneg(sub_x_rev)
            lemma_dts_neg_sub_swap(dts_mul(a, a), dts_mul(dd, dts_mul(b, b)));
            lemma_dts_neg_well_formed(dts_mul(a, a));
            lemma_dts_same_radicand_symmetric(
                dts_mul(a, a), dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_neg(dts_mul(a, a));
            lemma_dts_same_radicand_transitive(
                dts_mul(dd, dts_mul(b, b)), dts_mul(a, a),
                dts_neg(dts_mul(a, a)));
            lemma_dts_add_closed(
                dts_mul(dd, dts_mul(b, b)), dts_neg(dts_mul(a, a)));
            if !dts_nonneg_fuel(sub_x, f) {
                let neg_sub_x = dts_neg(sub_x);
                let sub_x_rev = dts_sub(
                    dts_mul(dd, dts_mul(b, b)), dts_mul(a, a));
                lemma_dts_same_radicand_neg(sub_x);
                lemma_dts_same_radicand_symmetric(sub_x, neg_sub_x);
                lemma_dts_same_radicand_symmetric(dts_mul(a, a), sub_x);
                lemma_dts_same_radicand_transitive(
                    neg_sub_x, sub_x, dts_mul(a, a));
                lemma_dts_same_radicand_transitive(
                    neg_sub_x, dts_mul(a, a),
                    dts_mul(dd, dts_mul(b, b)));
                lemma_dts_same_radicand_transitive(
                    neg_sub_x, dts_mul(dd, dts_mul(b, b)), sub_x_rev);
                lemma_dts_nonneg_fuel_congruence(neg_sub_x, sub_x_rev, f);
            }
            // Post-bridge: nonneg(sub_x) || nonneg(sub_x_rev)

            // Neg-square eqv/same_radicand symmetries for sub_congruence_both
            lemma_dts_eqv_symmetric(dts_mul(na, na), dts_mul(a, a));
            lemma_dts_eqv_symmetric(
                dts_mul(dd, dts_mul(nb, nb)), dts_mul(dd, dts_mul(b, b)));
            lemma_dts_same_radicand_symmetric(dts_mul(na, na), dts_mul(a, a));
            lemma_dts_same_radicand_symmetric(
                dts_mul(dd, dts_mul(nb, nb)), dts_mul(dd, dts_mul(b, b)));

            if a_nn {
                // Case A: a_nn, !b_nn, nb_nn, !na_nn
                if dts_nonneg_fuel(sub_x, f) {
                    // C2(x): a_nn && nonneg(neg(b)) && !is_zero(b) && nonneg(sub_x)
                    // nonneg(neg(b)) = nb_nn ✓ (from IH, since !b_nn → nb_nn)
                    // !is_zero(b): is_zero(b) → b_nn → contradiction
                    if dts_is_zero(b) {
                        lemma_dts_is_zero_implies_eqv_zero(b);
                        lemma_dts_nonneg_fuel_zero(b, f);
                    }
                    return; // C2(x)
                }
                // !nonneg(sub_x) → nonneg(sub_x_rev) from bridge
                // C3(neg): nonneg(neg(na)) && !is_zero(na) && nb_nn && !is_zero(nb)
                //        && nonneg(sub_nx_rev)
                // nonneg(neg(na)) = nonneg(neg(neg(a))): a_nn + involution
                // (already established in setup if a_nn block at lines above)
                // !is_zero(na): is_zero(na) → na_nn → contradiction
                if dts_is_zero(na) {
                    lemma_dts_is_zero_implies_eqv_zero(na);
                    lemma_dts_nonneg_fuel_zero(na, f);
                }
                // !is_zero(nb): is_zero(nb) → is_zero(b) → b_nn → contradiction
                if dts_is_zero(nb) {
                    lemma_dts_neg_preserves_is_zero(nb);
                    lemma_dts_neg_involution(b);
                    lemma_dts_is_zero_congruence(dts_neg(nb), b);
                    lemma_dts_is_zero_implies_eqv_zero(b);
                    lemma_dts_nonneg_fuel_zero(b, f);
                }
                // nonneg(sub_nx_rev) from nonneg(sub_x_rev) via neg_square
                // Re-establish neg_square eqv + same_radicand chains
                lemma_dts_neg_square(a);
                lemma_dts_neg_square(b);
                // same_radicand(nb², b²) chain
                lemma_dts_same_radicand_neg(b);
                lemma_dts_same_radicand_symmetric(b, nb);
                lemma_dts_mul_preserves_same_radicand_left(nb, b, nb);
                lemma_dts_mul_preserves_same_radicand_right(nb, b, b);
                lemma_dts_same_radicand_transitive(
                    dts_mul(nb, nb), dts_mul(b, nb), dts_mul(b, b));
                // same_radicand(na², a²) chain
                lemma_dts_same_radicand_neg(a);
                lemma_dts_same_radicand_symmetric(a, na);
                lemma_dts_mul_preserves_same_radicand_left(na, a, na);
                lemma_dts_mul_preserves_same_radicand_right(na, a, a);
                lemma_dts_same_radicand_transitive(
                    dts_mul(na, na), dts_mul(a, na), dts_mul(a, a));
                // eqv + same_radicand for dd*nb² vs dd*b²
                lemma_dts_mul_congruence_right(dts_mul(nb, nb), dts_mul(b, b), dd);
                lemma_dts_mul_preserves_same_radicand_right(
                    dts_mul(nb, nb), dts_mul(b, b), dd);
                // Symmetries needed for sub_congruence_both
                lemma_dts_eqv_symmetric(dts_mul(na, na), dts_mul(a, a));
                lemma_dts_eqv_symmetric(
                    dts_mul(dd, dts_mul(nb, nb)),
                    dts_mul(dd, dts_mul(b, b)));
                lemma_dts_same_radicand_symmetric(dts_mul(na, na), dts_mul(a, a));
                lemma_dts_same_radicand_symmetric(
                    dts_mul(dd, dts_mul(nb, nb)),
                    dts_mul(dd, dts_mul(b, b)));
                lemma_dts_sub_congruence_both(
                    dts_mul(dd, dts_mul(b, b)), dts_mul(a, a),
                    dts_mul(dd, dts_mul(nb, nb)), dts_mul(na, na));
                lemma_dts_nonneg_fuel_congruence(
                    dts_sub(dts_mul(dd, dts_mul(b, b)), dts_mul(a, a)),
                    dts_sub(dts_mul(dd, dts_mul(nb, nb)), dts_mul(na, na)), f);
                return; // C3(neg)
            } else {
                // Case D: !a_nn, na_nn, b_nn, !nb_nn
                let sub_x_rev = dts_sub(
                    dts_mul(dd, dts_mul(b, b)), dts_mul(a, a));
                if dts_nonneg_fuel(sub_x_rev, f) {
                    // C3(x): nonneg(neg(a)) && !is_zero(a) && b_nn && !is_zero(b)
                    //       && nonneg(sub_x_rev)
                    // nonneg(neg(a)) = na_nn ✓
                    // !is_zero(a): is_zero(a) → a_nn → contradiction
                    if dts_is_zero(a) {
                        lemma_dts_is_zero_implies_eqv_zero(a);
                        lemma_dts_nonneg_fuel_zero(a, f);
                    }
                    // !is_zero(b): is_zero(b) → is_zero(nb) → nb_nn → contradiction
                    //   (since na_nn && nb_nn → C1_neg, but C1_neg failed)
                    if dts_is_zero(b) {
                        lemma_dts_neg_preserves_is_zero(b);
                        lemma_dts_is_zero_implies_eqv_zero(nb);
                        lemma_dts_nonneg_fuel_zero(nb, f);
                    }
                    return; // C3(x)
                }
                // !nonneg(sub_x_rev) → nonneg(sub_x) from bridge (modus tollens)
                // C2(neg): na_nn && nonneg(neg(nb)) && !is_zero(nb) && nonneg(sub_nx)
                // nonneg(neg(nb)) = nonneg(neg(neg(b))): b_nn + involution
                // (already established in setup if b_nn block)
                // !is_zero(nb): is_zero(nb) → is_zero(b) → b_nn ✓, but also
                //   → nb_nn → na_nn && nb_nn → C1_neg failed → contradiction
                if dts_is_zero(nb) {
                    lemma_dts_neg_preserves_is_zero(nb);
                    lemma_dts_neg_involution(b);
                    lemma_dts_is_zero_congruence(dts_neg(nb), b);
                    lemma_dts_is_zero_implies_eqv_zero(nb);
                    lemma_dts_nonneg_fuel_zero(nb, f);
                }
                // nonneg(sub_nx) from nonneg(sub_x) via neg_square
                // Re-establish neg_square eqv + same_radicand chains
                lemma_dts_neg_square(a);
                lemma_dts_neg_square(b);
                lemma_dts_same_radicand_neg(b);
                lemma_dts_same_radicand_symmetric(b, nb);
                lemma_dts_mul_preserves_same_radicand_left(nb, b, nb);
                lemma_dts_mul_preserves_same_radicand_right(nb, b, b);
                lemma_dts_same_radicand_transitive(
                    dts_mul(nb, nb), dts_mul(b, nb), dts_mul(b, b));
                lemma_dts_same_radicand_neg(a);
                lemma_dts_same_radicand_symmetric(a, na);
                lemma_dts_mul_preserves_same_radicand_left(na, a, na);
                lemma_dts_mul_preserves_same_radicand_right(na, a, a);
                lemma_dts_same_radicand_transitive(
                    dts_mul(na, na), dts_mul(a, na), dts_mul(a, a));
                lemma_dts_mul_congruence_right(dts_mul(nb, nb), dts_mul(b, b), dd);
                lemma_dts_mul_preserves_same_radicand_right(
                    dts_mul(nb, nb), dts_mul(b, b), dd);
                lemma_dts_eqv_symmetric(dts_mul(na, na), dts_mul(a, a));
                lemma_dts_eqv_symmetric(
                    dts_mul(dd, dts_mul(nb, nb)),
                    dts_mul(dd, dts_mul(b, b)));
                lemma_dts_same_radicand_symmetric(dts_mul(na, na), dts_mul(a, a));
                lemma_dts_same_radicand_symmetric(
                    dts_mul(dd, dts_mul(nb, nb)),
                    dts_mul(dd, dts_mul(b, b)));
                lemma_dts_sub_congruence_both(
                    dts_mul(a, a), dts_mul(dd, dts_mul(b, b)),
                    dts_mul(na, na), dts_mul(dd, dts_mul(nb, nb)));
                lemma_dts_nonneg_fuel_congruence(
                    sub_x,
                    dts_sub(dts_mul(na, na), dts_mul(dd, dts_mul(nb, nb))), f);
                return; // C2(neg)
            }
        }
    }
}

/// Multiplication is eqv-commutative for well-formed values with same radicand.
pub proof fn lemma_dts_mul_commutative(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures dts_eqv(dts_mul(a, b), dts_mul(b, a)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            verus_rational::rational::Rational::axiom_mul_commutative(r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, d1), DynTowerSpec::Ext(re2, im2, _)) => {
            let a1 = *re1; let b1 = *im1; let dd = *d1;
            let a2 = *re2; let b2 = *im2;
            // same_radicand(Ext, Ext) gives same_radicand(a1,a2), same_radicand(b1,b2)
            // well_formed gives same_radicand(a1,b1), same_radicand(a1,d1)
            // Cross same_radicand chains from well_formed + same_radicand
            // a1~b1 (well_formed a), b1~b2 (same_radicand a,b) → a1~b2
            lemma_dts_same_radicand_transitive(a1, b1, b2);
            // b1~a1 (symmetric), a1~a2 → b1~a2
            lemma_dts_same_radicand_symmetric(a1, b1);
            lemma_dts_same_radicand_transitive(b1, a1, a2);
            // b2~b1 (symmetric), b1~a2 → b2~a2. But need b2~b1 first.
            lemma_dts_same_radicand_symmetric(b1, b2);
            lemma_dts_same_radicand_transitive(b2, b1, a2);
            // IH: commutative for all 4 sub-term pairs
            lemma_dts_mul_commutative(a1, a2);
            lemma_dts_mul_commutative(b1, b2);
            lemma_dts_mul_commutative(a1, b2);
            lemma_dts_same_radicand_symmetric(b1, a2);
            lemma_dts_mul_commutative(b1, a2);
            // re: add(mul(a1,a2), mul(d,mul(b1,b2))) ≡ add(mul(a2,a1), mul(d,mul(b2,b1)))
            // same_radicand for mul_closed + mul_congruence
            lemma_dts_same_radicand_symmetric(b2, b1);
            lemma_dts_mul_closed(b1, b2);
            lemma_dts_mul_closed(b2, b1);
            lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, b2));
            lemma_dts_same_radicand_symmetric(b2, dts_mul(b2, b1));
            lemma_dts_same_radicand_transitive(dts_mul(b1, b2), b1, b2);
            lemma_dts_same_radicand_transitive(dts_mul(b1, b2), b2, dts_mul(b2, b1));
            lemma_dts_mul_congruence_right(dts_mul(b1, b2), dts_mul(b2, b1), dd);
            // Chain for re
            lemma_dts_add_congruence_left(
                dts_mul(a1, a2), dts_mul(a2, a1), dts_mul(dd, dts_mul(b1, b2)));
            lemma_dts_add_congruence_right(
                dts_mul(a2, a1),
                dts_mul(dd, dts_mul(b1, b2)), dts_mul(dd, dts_mul(b2, b1)));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(a1, a2), dts_mul(dd, dts_mul(b1, b2))),
                dts_add(dts_mul(a2, a1), dts_mul(dd, dts_mul(b1, b2))),
                dts_add(dts_mul(a2, a1), dts_mul(dd, dts_mul(b2, b1))));
            // im: add(mul(a1,b2), mul(b1,a2)) ≡ add(mul(a2,b1), mul(b2,a1))
            // A=mul(a1,b2)≡mul(b2,a1)=D, B=mul(b1,a2)≡mul(a2,b1)=C → add(A,B)≡add(C,D)
            lemma_dts_add_congruence_left(
                dts_mul(a1, b2), dts_mul(b2, a1), dts_mul(b1, a2));
            lemma_dts_add_congruence_right(
                dts_mul(b2, a1), dts_mul(b1, a2), dts_mul(a2, b1));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(a1, b2), dts_mul(b1, a2)),
                dts_add(dts_mul(b2, a1), dts_mul(b1, a2)),
                dts_add(dts_mul(b2, a1), dts_mul(a2, b1)));
            lemma_dts_add_commutative(dts_mul(b2, a1), dts_mul(a2, b1));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(a1, b2), dts_mul(b1, a2)),
                dts_add(dts_mul(b2, a1), dts_mul(a2, b1)),
                dts_add(dts_mul(a2, b1), dts_mul(b2, a1)));
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_mul_commutative(DynTowerSpec::Rat(r), *re);
            lemma_dts_mul_commutative(DynTowerSpec::Rat(r), *im);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_mul_commutative(*re, DynTowerSpec::Rat(r));
            lemma_dts_mul_commutative(*im, DynTowerSpec::Rat(r));
        }
    }
}

/// Embedding preserves non-zeroness: if a rational is nonzero, its DTS embedding is nonzero.
pub proof fn lemma_dts_rational_nonzero_preserved(r: Rational)
    requires !r.eqv(Rational::from_int_spec(0)),
    ensures !dts_is_zero(DynTowerSpec::Rat(r)),
{
    // dts_is_zero(Rat(r)) = r.eqv(0). Direct from requires.
}

/// nonneg_conclude_re: if re ≥ 0 and norm = re²-d·im² ≥ 0, then Ext(re,im,d) is nonneg.
/// Uses inner fuel f (nonneg_fuel at depth n-1). Result is nonneg at fuel f+1.
pub proof fn lemma_dts_nonneg_conclude_re_fuel(
    re: DynTowerSpec, im: DynTowerSpec, d: DynTowerSpec, f: nat,
)
    requires
        f >= dts_depth(re) + 1,
        f >= dts_depth(im) + 1,
        dts_well_formed(re), dts_well_formed(im),
        dts_nonneg_fuel(re, f),
        dts_nonneg_fuel(
            dts_sub(dts_mul(re, re), dts_mul(d, dts_mul(im, im))), f),
    ensures
        dts_nonneg_fuel(
            DynTowerSpec::Ext(Box::new(re), Box::new(im), Box::new(d)),
            (f + 1) as nat),
{
    lemma_dts_nonneg_or_neg_nonneg_fuel(im, f);
    if dts_nonneg_fuel(im, f) {
        // C1: nonneg(re) && nonneg(im) ✓
    } else {
        // C2: nonneg(re) && nonneg(neg(im)) && !is_zero(im) && nonneg(norm)
        if dts_is_zero(im) {
            lemma_dts_is_zero_implies_eqv_zero(im);
            lemma_dts_nonneg_fuel_zero(im, f);
        }
    }
}

/// nonneg_conclude_im: if im > 0 and norm ≤ 0, then Ext(re,im,d) is nonneg.
/// Requires !is_zero(im) to handle C3's b_pos condition.
pub proof fn lemma_dts_nonneg_conclude_im_fuel(
    re: DynTowerSpec, im: DynTowerSpec, d: DynTowerSpec, f: nat,
)
    requires
        f >= dts_depth(re) + 1,
        f >= dts_depth(im) + 1,
        dts_well_formed(re), dts_well_formed(im),
        dts_nonneg_fuel(im, f),
        !dts_is_zero(im),
        dts_nonneg_fuel(
            dts_sub(dts_mul(d, dts_mul(im, im)), dts_mul(re, re)), f),
    ensures
        dts_nonneg_fuel(
            DynTowerSpec::Ext(Box::new(re), Box::new(im), Box::new(d)),
            (f + 1) as nat),
{
    lemma_dts_nonneg_or_neg_nonneg_fuel(re, f);
    if dts_nonneg_fuel(re, f) {
        // C1: nonneg(re) && nonneg(im) ✓
    } else {
        // C3: nonneg(neg(re)) && !is_zero(re) && nonneg(im) && !is_zero(im)
        //   && nonneg(d·im²-re²)
        if dts_is_zero(re) {
            lemma_dts_is_zero_implies_eqv_zero(re);
            lemma_dts_nonneg_fuel_zero(re, f);
        }
        // !is_zero(re) ✓, !is_zero(im) ✓ (from requires), nonneg(im) ✓, nonneg(norm_rev) ✓
    }
}

/// Add exchange: (a+b)+(c+d) ≡ (a+c)+(b+d). Uses AdditiveCommutativeMonoid axioms.
pub proof fn lemma_dts_add_exchange(a: DynTowerSpec, b: DynTowerSpec,
    c: DynTowerSpec, d: DynTowerSpec)
    ensures dts_eqv(dts_add(dts_add(a, b), dts_add(c, d)),
                     dts_add(dts_add(a, c), dts_add(b, d))),
{
    // (a+b)+(c+d) ≡ a+(b+(c+d)) [assoc]
    DynTowerSpec::axiom_add_associative(a, b, dts_add(c, d));
    // b+(c+d) ≡ (b+c)+d [assoc, symmetric]
    DynTowerSpec::axiom_add_associative(b, c, d);
    DynTowerSpec::axiom_eqv_symmetric(dts_add(dts_add(b, c), d), dts_add(b, dts_add(c, d)));
    lemma_dts_add_congruence_right(a, dts_add(b, dts_add(c, d)), dts_add(dts_add(b, c), d));
    // a+((b+c)+d): commute b+c → c+b
    DynTowerSpec::axiom_add_commutative(b, c);
    lemma_dts_add_congruence_left(dts_add(b, c), dts_add(c, b), d);
    lemma_dts_add_congruence_right(a, dts_add(dts_add(b, c), d), dts_add(dts_add(c, b), d));
    // a+((c+b)+d) ≡ a+(c+(b+d)) [assoc]
    DynTowerSpec::axiom_add_associative(c, b, d);
    lemma_dts_add_congruence_right(a, dts_add(dts_add(c, b), d), dts_add(c, dts_add(b, d)));
    // a+(c+(b+d)) ≡ (a+c)+(b+d) [assoc, symmetric]
    DynTowerSpec::axiom_add_associative(a, c, dts_add(b, d));
    DynTowerSpec::axiom_eqv_symmetric(
        dts_add(dts_add(a, c), dts_add(b, d)),
        dts_add(a, dts_add(c, dts_add(b, d))));
    // Chain all steps
    lemma_dts_eqv_transitive(
        dts_add(dts_add(a, b), dts_add(c, d)),
        dts_add(a, dts_add(b, dts_add(c, d))),
        dts_add(a, dts_add(dts_add(b, c), d)));
    lemma_dts_eqv_transitive(
        dts_add(dts_add(a, b), dts_add(c, d)),
        dts_add(a, dts_add(dts_add(b, c), d)),
        dts_add(a, dts_add(dts_add(c, b), d)));
    lemma_dts_eqv_transitive(
        dts_add(dts_add(a, b), dts_add(c, d)),
        dts_add(a, dts_add(dts_add(c, b), d)),
        dts_add(a, dts_add(c, dts_add(b, d))));
    lemma_dts_eqv_transitive(
        dts_add(dts_add(a, b), dts_add(c, d)),
        dts_add(a, dts_add(c, dts_add(b, d))),
        dts_add(dts_add(a, c), dts_add(b, d)));
}

/// neg distributes over add: neg(a+b) ≡ neg(a) + neg(b).
/// Uses the generic AdditiveGroup lemma since DTS implements AdditiveGroup.
pub proof fn lemma_dts_neg_add(a: DynTowerSpec, b: DynTowerSpec)
    ensures dts_eqv(dts_neg(dts_add(a, b)), dts_add(dts_neg(a), dts_neg(b))),
{
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<DynTowerSpec>(a, b);
}

/// neg_mul_right: mul(a, neg(b)) ≡ neg(mul(a, b)).
/// Self-contained structural induction — d sub-field calls always decrease.
pub proof fn lemma_dts_neg_mul_right(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures dts_eqv(dts_mul(a, dts_neg(b)), dts_neg(dts_mul(a, b))),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            Rational::lemma_denom_positive(r1);
            Rational::lemma_denom_positive(r2);
            assert(r1.mul_spec(r2.neg_spec()).num
                == r1.mul_spec(r2).neg_spec().num) by (nonlinear_arith);
            assert(r1.mul_spec(r2.neg_spec()).den
                == r1.mul_spec(r2).neg_spec().den) by (nonlinear_arith);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_neg_mul_right(*re, DynTowerSpec::Rat(r));
            lemma_dts_neg_mul_right(*im, DynTowerSpec::Rat(r));
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_neg_mul_right(DynTowerSpec::Rat(r), *re);
            lemma_dts_neg_mul_right(DynTowerSpec::Rat(r), *im);
        }
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            // mul(Ext(a,b,d), neg(Ext(c,e,_))) = mul(Ext(a,b,d), Ext(neg(c),neg(e),_))
            // = Ext(a*neg(c) + d*b*neg(e), a*neg(e) + b*neg(c), d)
            // neg(mul(Ext(a,b,d), Ext(c,e,_))) = neg(Ext(a*c+d*b*e, a*e+b*c, d))
            // = Ext(neg(a*c+d*b*e), neg(a*e+b*c), d)
            // Cross same_radicand
            lemma_dts_same_radicand_transitive(*re1, *im1, *im2);
            lemma_dts_same_radicand_symmetric(*re1, *im1);
            lemma_dts_same_radicand_transitive(*im1, *re1, *re2);
            // neg preserves
            lemma_dts_neg_well_formed(*re2);
            lemma_dts_neg_well_formed(*im2);
            lemma_dts_same_radicand_neg(*re2);
            lemma_dts_same_radicand_neg(*im2);
            lemma_dts_same_radicand_symmetric(*re2, dts_neg(*re2));
            lemma_dts_same_radicand_transitive(*re1, *re2, dts_neg(*re2));
            lemma_dts_same_radicand_transitive(*re1, *im2, dts_neg(*im2));
            lemma_dts_same_radicand_symmetric(*im2, dts_neg(*im2));
            lemma_dts_same_radicand_transitive(*im1, *im2, dts_neg(*im2));
            lemma_dts_same_radicand_transitive(*im1, *re2, dts_neg(*re2));
            lemma_dts_same_radicand_symmetric(*re2, dts_neg(*re2));
            // IH for sub-term pairs
            lemma_dts_neg_mul_right(*re1, *re2);
            lemma_dts_neg_mul_right(*im1, *im2);
            lemma_dts_neg_mul_right(*re1, *im2);
            lemma_dts_neg_mul_right(*im1, *re2);
            // d*b*neg(e): IH gives b*neg(e) ≡ neg(b*e)
            // mul_congruence propagates through d*: d*(b*neg(e)) ≡ d*neg(b*e)
            lemma_dts_mul_closed(*im1, *im2);
            lemma_dts_mul_closed(*im1, dts_neg(*im2));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, dts_neg(*im2)));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_neg(*im2)), *im1, dts_mul(*im1, *im2));
            lemma_dts_neg_well_formed(dts_mul(*im1, *im2));
            lemma_dts_same_radicand_neg(dts_mul(*im1, *im2));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_neg(*im2)), dts_mul(*im1, *im2),
                dts_neg(dts_mul(*im1, *im2)));
            lemma_dts_mul_congruence_right(
                dts_mul(*im1, dts_neg(*im2)), dts_neg(dts_mul(*im1, *im2)), *d);
            // d*neg(b*e) ≡ neg(d*b*e): neg_mul_right(d, b*e) — d is sub-field, valid!
            lemma_dts_same_radicand_symmetric(*re1, *d);
            lemma_dts_same_radicand_transitive(*d, *re1, *im1);
            lemma_dts_same_radicand_transitive(*d, *im1, dts_mul(*im1, *im2));
            lemma_dts_neg_mul_right(*d, dts_mul(*im1, *im2));
            // Chain for d*b*neg(e) ≡ neg(d*b*e):
            //   d*b*neg(e) ≡ d*neg(b*e) [congruence, done above]
            //   d*neg(b*e) ≡ neg(d*b*e) [neg_mul_right, done above]
            lemma_dts_eqv_transitive(
                dts_mul(*d, dts_mul(*im1, dts_neg(*im2))),
                dts_mul(*d, dts_neg(dts_mul(*im1, *im2))),
                dts_neg(dts_mul(*d, dts_mul(*im1, *im2))));
            // neg_add for RHS decomposition
            lemma_dts_neg_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            lemma_dts_neg_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2));
            // Explicit add_congruence for re: LHS_re ≡ RHS_re
            lemma_dts_add_congruence_left(
                dts_mul(*re1, dts_neg(*re2)), dts_neg(dts_mul(*re1, *re2)),
                dts_mul(*d, dts_mul(*im1, dts_neg(*im2))));
            lemma_dts_add_congruence_right(
                dts_neg(dts_mul(*re1, *re2)),
                dts_mul(*d, dts_mul(*im1, dts_neg(*im2))),
                dts_neg(dts_mul(*d, dts_mul(*im1, *im2))));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(*re1, dts_neg(*re2)), dts_mul(*d, dts_mul(*im1, dts_neg(*im2)))),
                dts_add(dts_neg(dts_mul(*re1, *re2)), dts_mul(*d, dts_mul(*im1, dts_neg(*im2)))),
                dts_add(dts_neg(dts_mul(*re1, *re2)), dts_neg(dts_mul(*d, dts_mul(*im1, *im2)))));
            // Explicit add_congruence for im:
            // IH: re1*neg(im2) ≡ neg(re1*im2) AND im1*neg(re2) ≡ neg(im1*re2)
            // → add(re1*neg(im2), im1*neg(re2)) ≡ add(neg(re1*im2), neg(im1*re2))
            lemma_dts_add_congruence_left(
                dts_mul(*re1, dts_neg(*im2)), dts_neg(dts_mul(*re1, *im2)),
                dts_mul(*im1, dts_neg(*re2)));
            lemma_dts_add_congruence_right(
                dts_neg(dts_mul(*re1, *im2)),
                dts_mul(*im1, dts_neg(*re2)),
                dts_neg(dts_mul(*im1, *re2)));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(*re1, dts_neg(*im2)), dts_mul(*im1, dts_neg(*re2))),
                dts_add(dts_neg(dts_mul(*re1, *im2)), dts_mul(*im1, dts_neg(*re2))),
                dts_add(dts_neg(dts_mul(*re1, *im2)), dts_neg(dts_mul(*im1, *re2))));
            // Final: connect intermediate ≡ RHS via symmetric neg_add
            // re: intermediate ≡ neg(add(A,B)) where intermediate = add(neg(A),neg(B))
            lemma_dts_eqv_symmetric(
                dts_neg(dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)))),
                dts_add(dts_neg(dts_mul(*re1, *re2)), dts_neg(dts_mul(*d, dts_mul(*im1, *im2)))));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(*re1, dts_neg(*re2)), dts_mul(*d, dts_mul(*im1, dts_neg(*im2)))),
                dts_add(dts_neg(dts_mul(*re1, *re2)), dts_neg(dts_mul(*d, dts_mul(*im1, *im2)))),
                dts_neg(dts_add(dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)))));
            // im: similarly
            lemma_dts_eqv_symmetric(
                dts_neg(dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2))),
                dts_add(dts_neg(dts_mul(*re1, *im2)), dts_neg(dts_mul(*im1, *re2))));
            lemma_dts_eqv_transitive(
                dts_add(dts_mul(*re1, dts_neg(*im2)), dts_mul(*im1, dts_neg(*re2))),
                dts_add(dts_neg(dts_mul(*re1, *im2)), dts_neg(dts_mul(*im1, *re2))),
                dts_neg(dts_add(dts_mul(*re1, *im2), dts_mul(*im1, *re2))));
        }
    }
}

/// neg_mul_left: mul(neg(a), b) ≡ neg(mul(a, b)).
/// Derived from neg_mul_right + mul_commutative + neg_congruence.
pub proof fn lemma_dts_neg_mul_left(a: DynTowerSpec, b: DynTowerSpec)
    requires dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures dts_eqv(dts_mul(dts_neg(a), b), dts_neg(dts_mul(a, b))),
{
    // mul(neg(a), b) ≡ mul(b, neg(a))  [commutative]
    lemma_dts_neg_well_formed(a);
    lemma_dts_same_radicand_neg(a);
    lemma_dts_same_radicand_symmetric(a, dts_neg(a));
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, dts_neg(a));
    lemma_dts_same_radicand_symmetric(b, dts_neg(a));
    lemma_dts_mul_commutative(dts_neg(a), b);
    // mul(b, neg(a)) ≡ neg(mul(b, a))  [neg_mul_right]
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_neg_mul_right(b, a);
    // neg(mul(b, a)) ≡ neg(mul(a, b))  [neg_congruence + commutative]
    lemma_dts_mul_commutative(a, b);
    lemma_dts_eqv_symmetric(dts_mul(a, b), dts_mul(b, a));
    lemma_dts_neg_congruence(dts_mul(b, a), dts_mul(a, b));
    // Chain
    lemma_dts_eqv_transitive(
        dts_mul(dts_neg(a), b), dts_mul(b, dts_neg(a)),
        dts_neg(dts_mul(b, a)));
    lemma_dts_eqv_transitive(
        dts_mul(dts_neg(a), b), dts_neg(dts_mul(b, a)),
        dts_neg(dts_mul(a, b)));
}

/// Left distributivity: mul(a, add(b, c)) ≡ add(mul(a, b), mul(a, c)).
/// Requires well_formed + same_radicand for mul_congruence in Ext×Ext×Ext case.
pub proof fn lemma_dts_mul_distributes_left(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
        dts_same_radicand(a, b), dts_same_radicand(b, c),
    ensures dts_eqv(dts_mul(a, dts_add(b, c)), dts_add(dts_mul(a, b), dts_mul(a, c))),
    decreases a, b, c,
{
    lemma_dts_same_radicand_transitive(a, b, c);
    match (a, b, c) {
        (DynTowerSpec::Rat(r), DynTowerSpec::Rat(s), DynTowerSpec::Rat(t)) => {
            Rational::axiom_mul_distributes_left(r, s, t);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_mul_distributes_left(DynTowerSpec::Rat(r), *re1, *re2);
            lemma_dts_mul_distributes_left(DynTowerSpec::Rat(r), *im1, *im2);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(s), DynTowerSpec::Rat(t)) => {
            lemma_dts_mul_distributes_left(*re, DynTowerSpec::Rat(s), DynTowerSpec::Rat(t));
            lemma_dts_mul_distributes_left(*im, DynTowerSpec::Rat(s), DynTowerSpec::Rat(t));
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Rat(s), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_mul_distributes_left(DynTowerSpec::Rat(r), DynTowerSpec::Rat(s), *re);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(t)) => {
            lemma_dts_mul_distributes_left(DynTowerSpec::Rat(r), *re, DynTowerSpec::Rat(t));
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(s), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_mul_distributes_left(*re, DynTowerSpec::Rat(s), *re2);
            lemma_dts_mul_distributes_left(*im, DynTowerSpec::Rat(s), *im2);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Ext(re2, im2, _), DynTowerSpec::Rat(t)) => {
            lemma_dts_mul_distributes_left(*re, *re2, DynTowerSpec::Rat(t));
            lemma_dts_mul_distributes_left(*im, *im2, DynTowerSpec::Rat(t));
        }
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _), DynTowerSpec::Ext(re3, im3, _)) => {
            // Cross same_radicand for all sub-term pairs
            lemma_dts_same_radicand_transitive(*re1, *im1, *im2);
            lemma_dts_same_radicand_symmetric(*re1, *im1);
            lemma_dts_same_radicand_transitive(*im1, *re1, *re2);
            lemma_dts_same_radicand_transitive(*re1, *re2, *re3);
            lemma_dts_same_radicand_transitive(*re1, *im2, *im3);
            lemma_dts_same_radicand_transitive(*im1, *re2, *re3);
            lemma_dts_same_radicand_transitive(*im1, *im2, *im3);
            lemma_dts_same_radicand_symmetric(*re1, *d);
            lemma_dts_same_radicand_transitive(*d, *re1, *im1);
            // IH distributes for all sub-term triples
            lemma_dts_mul_distributes_left(*re1, *re2, *re3);
            lemma_dts_mul_distributes_left(*re1, *im2, *im3);
            lemma_dts_mul_distributes_left(*im1, *re2, *re3);
            lemma_dts_mul_distributes_left(*im1, *im2, *im3);
            // d*(b*(e1+e2)): propagate IH through d via congruence + distributes
            // b*(e1+e2) ≡ b*e1+b*e2 [IH]. Congruence: d*(b*(e1+e2)) ≡ d*(b*e1+b*e2)
            lemma_dts_mul_closed(*im1, *im2);
            lemma_dts_mul_closed(*im1, *im3);
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *im3));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, *im2), *im1, dts_mul(*im1, *im3));
            lemma_dts_add_closed(dts_mul(*im1, *im2), dts_mul(*im1, *im3));
            lemma_dts_same_radicand_symmetric(
                dts_mul(*im1, *im2),
                dts_add(dts_mul(*im1, *im2), dts_mul(*im1, *im3)));
            // mul_closed(im1, add(im2,im3)): establish all preconditions explicitly
            assert(dts_well_formed(*im2));
            assert(dts_well_formed(*im3));
            assert(dts_same_radicand(*im2, *im3));
            lemma_dts_add_closed(*im2, *im3);
            assert(dts_well_formed(dts_add(*im2, *im3)));
            assert(dts_same_radicand(*im2, dts_add(*im2, *im3)));
            assert(dts_same_radicand(*im1, *im2));
            lemma_dts_same_radicand_transitive(*im1, *im2, dts_add(*im2, *im3));
            assert(dts_same_radicand(*im1, dts_add(*im2, *im3)));
            assert(dts_well_formed(*im1));
            lemma_dts_mul_closed(*im1, dts_add(*im2, *im3));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, dts_add(*im2, *im3)));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_add(*im2, *im3)), *im1,
                dts_mul(*im1, *im2));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_add(*im2, *im3)),
                dts_mul(*im1, *im2),
                dts_add(dts_mul(*im1, *im2), dts_mul(*im1, *im3)));
            lemma_dts_mul_congruence_right(
                dts_mul(*im1, dts_add(*im2, *im3)),
                dts_add(dts_mul(*im1, *im2), dts_mul(*im1, *im3)), *d);
            // d*(b*e1+b*e2) ≡ d*b*e1 + d*b*e2 [distributes_left on d]
            lemma_dts_same_radicand_transitive(*d, *im1, dts_mul(*im1, *im2));
            lemma_dts_same_radicand_transitive(*d, dts_mul(*im1, *im2), dts_mul(*im1, *im3));
            lemma_dts_mul_distributes_left(*d, dts_mul(*im1, *im2), dts_mul(*im1, *im3));
            // Chain d*b*(e1+e2) ≡ d*(b*e1+b*e2) ≡ d*b*e1+d*b*e2
            lemma_dts_eqv_transitive(
                dts_mul(*d, dts_mul(*im1, dts_add(*im2, *im3))),
                dts_mul(*d, dts_add(dts_mul(*im1, *im2), dts_mul(*im1, *im3))),
                dts_add(dts_mul(*d, dts_mul(*im1, *im2)), dts_mul(*d, dts_mul(*im1, *im3))));
            // Same for im's d*b*(c1+c2) chain
            lemma_dts_mul_closed(*im1, *re2);
            lemma_dts_mul_closed(*im1, *re3);
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *re2));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, *re3));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, *re2), *im1, dts_mul(*im1, *re3));
            lemma_dts_add_closed(dts_mul(*im1, *re2), dts_mul(*im1, *re3));
            lemma_dts_same_radicand_symmetric(
                dts_mul(*im1, *re2),
                dts_add(dts_mul(*im1, *re2), dts_mul(*im1, *re3)));
            lemma_dts_add_closed(*re2, *re3);
            lemma_dts_same_radicand_symmetric(*re2, dts_add(*re2, *re3));
            lemma_dts_same_radicand_symmetric(*im1, *re2);
            lemma_dts_same_radicand_transitive(*im1, *re2, dts_add(*re2, *re3));
            lemma_dts_same_radicand_symmetric(*im1, dts_add(*re2, *re3));
            lemma_dts_mul_closed(*im1, dts_add(*re2, *re3));
            lemma_dts_same_radicand_symmetric(*im1, dts_mul(*im1, dts_add(*re2, *re3)));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_add(*re2, *re3)), *im1,
                dts_mul(*im1, *re2));
            lemma_dts_same_radicand_transitive(
                dts_mul(*im1, dts_add(*re2, *re3)),
                dts_mul(*im1, *re2),
                dts_add(dts_mul(*im1, *re2), dts_mul(*im1, *re3)));
            lemma_dts_mul_congruence_right(
                dts_mul(*im1, dts_add(*re2, *re3)),
                dts_add(dts_mul(*im1, *re2), dts_mul(*im1, *re3)), *d);
            lemma_dts_same_radicand_transitive(*d, *im1, dts_mul(*im1, *re2));
            lemma_dts_same_radicand_transitive(*d, dts_mul(*im1, *re2), dts_mul(*im1, *re3));
            lemma_dts_mul_distributes_left(*d, dts_mul(*im1, *re2), dts_mul(*im1, *re3));
            lemma_dts_eqv_transitive(
                dts_mul(*d, dts_mul(*im1, dts_add(*re2, *re3))),
                dts_mul(*d, dts_add(dts_mul(*im1, *re2), dts_mul(*im1, *re3))),
                dts_add(dts_mul(*d, dts_mul(*im1, *re2)), dts_mul(*d, dts_mul(*im1, *re3))));
            // Now combine: re = a*(c1+c2) + d*b*(e1+e2)
            // ≡ (a*c1+a*c2) + (d*b*e1+d*b*e2) via add_congruence from IH + chain
            lemma_dts_add_congruence_left(
                dts_mul(*re1, dts_add(*re2, *re3)),
                dts_add(dts_mul(*re1, *re2), dts_mul(*re1, *re3)),
                dts_mul(*d, dts_mul(*im1, dts_add(*im2, *im3))));
            lemma_dts_add_congruence_right(
                dts_add(dts_mul(*re1, *re2), dts_mul(*re1, *re3)),
                dts_mul(*d, dts_mul(*im1, dts_add(*im2, *im3))),
                dts_add(dts_mul(*d, dts_mul(*im1, *im2)), dts_mul(*d, dts_mul(*im1, *im3))));
            // ═══ Final re chain: LHS_re → step1 → step2 → RHS_re ═══
            let lhs_re = dts_add(
                dts_mul(*re1, dts_add(*re2, *re3)),
                dts_mul(*d, dts_mul(*im1, dts_add(*im2, *im3))));
            let ra = dts_mul(*re1, *re2); let rb = dts_mul(*re1, *re3);
            let rc = dts_mul(*d, dts_mul(*im1, *im2));
            let rd = dts_mul(*d, dts_mul(*im1, *im3));
            let step1_re = dts_add(dts_add(ra, rb),
                dts_mul(*d, dts_mul(*im1, dts_add(*im2, *im3))));
            let step2_re = dts_add(dts_add(ra, rb), dts_add(rc, rd));
            let rhs_re = dts_add(dts_add(ra, rc), dts_add(rb, rd));
            // LHS_re → step1 (congruence left: distribute a*(c1+c2))
            // step1 → step2 (congruence right: distribute+chain d*b*(e1+e2))
            // step2 → rhs_re (exchange)
            lemma_dts_eqv_transitive(lhs_re, step1_re, step2_re);
            lemma_dts_add_exchange(ra, rb, rc, rd);
            lemma_dts_eqv_transitive(lhs_re, step2_re, rhs_re);

            // ═══ Final im chain: LHS_im → step1 → RHS_im ═══
            // im of mul(Ext(a,b,d), Ext(c,e,_)) = ae + bc (no d factor!)
            let ia = dts_mul(*re1, *im2); let ib = dts_mul(*re1, *im3);
            let ic = dts_mul(*im1, *re2); let id = dts_mul(*im1, *re3);
            let lhs_im = dts_add(
                dts_mul(*re1, dts_add(*im2, *im3)),
                dts_mul(*im1, dts_add(*re2, *re3)));
            let step1_im = dts_add(dts_add(ia, ib), dts_mul(*im1, dts_add(*re2, *re3)));
            let step2_im = dts_add(dts_add(ia, ib), dts_add(ic, id));
            let rhs_im = dts_add(dts_add(ia, ic), dts_add(ib, id));
            lemma_dts_add_congruence_left(
                dts_mul(*re1, dts_add(*im2, *im3)),
                dts_add(ia, ib),
                dts_mul(*im1, dts_add(*re2, *re3)));
            lemma_dts_add_congruence_right(
                dts_add(ia, ib),
                dts_mul(*im1, dts_add(*re2, *re3)),
                dts_add(ic, id));
            lemma_dts_eqv_transitive(lhs_im, step1_im, step2_im);
            lemma_dts_add_exchange(ia, ib, ic, id);
            lemma_dts_eqv_transitive(lhs_im, step2_im, rhs_im);
        }
    }
}

/// Difference of squares: b²-a² ≡ (b-a)(b+a).
/// Key helper for square_le_square and nonneg_add norm bounds.
#[verifier::rlimit(60)]
pub proof fn lemma_dts_difference_of_squares(a: DynTowerSpec, b: DynTowerSpec)
    requires
        dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
    ensures
        dts_eqv(
            dts_sub(dts_mul(b, b), dts_mul(a, a)),
            dts_mul(dts_sub(b, a), dts_add(b, a))),
{
    let na = dts_neg(a);
    let ba = dts_sub(b, a); // = add(b, neg(a))
    let bpa = dts_add(b, a);
    let ab = dts_mul(a, b);
    let b2 = dts_mul(b, b);
    let a2 = dts_mul(a, a);
    // Setup: well_formed and same_radicand chains
    lemma_dts_neg_well_formed(a);
    lemma_dts_same_radicand_reflexive(a);
    lemma_dts_same_radicand_neg(a);
    lemma_dts_same_radicand_symmetric(a, na);
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, na);
    lemma_dts_add_closed(b, na);
    lemma_dts_add_closed(b, a);
    lemma_dts_same_radicand_symmetric(b, ba);
    lemma_dts_same_radicand_symmetric(b, bpa);
    lemma_dts_same_radicand_transitive(ba, b, bpa);
    lemma_dts_same_radicand_transitive(ba, b, a);
    lemma_dts_same_radicand_transitive(ba, b, na);

    // Step 1: (b-a)(b+a) ≡ (b-a)*b + (b-a)*a  [distributes_left]
    lemma_dts_mul_distributes_left(ba, b, a);

    // Step 2: (b-a)*b: commutative → b*(b+neg(a)), then distributes
    lemma_dts_same_radicand_reflexive(b);
    lemma_dts_same_radicand_transitive(b, a, na);
    lemma_dts_mul_commutative(ba, b);
    lemma_dts_mul_distributes_left(b, b, na);
    // mul(b, add(b, na)) ≡ add(b², b*neg(a))
    lemma_dts_neg_mul_right(b, a);
    // b*neg(a) ≡ neg(b*a)
    lemma_dts_mul_commutative(b, a);
    // b*a ≡ a*b

    // Step 3: (b-a)*a: commutative → a*(b+neg(a)), then distributes
    lemma_dts_same_radicand_symmetric(ba, a);
    lemma_dts_mul_commutative(ba, a);
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(a, b, na);
    lemma_dts_mul_distributes_left(a, b, na);
    // mul(a, add(b, na)) ≡ add(a*b, a*na)
    lemma_dts_neg_mul_right(a, a);
    // a*neg(a) ≡ neg(a*a) = neg(a²)

    // Step 4: (b-a)(b+a) ≡ add(add(b², neg(ab)), add(ab, neg(a²)))
    // By add_exchange: ≡ add(add(b², ab), add(neg(ab), neg(a²)))
    // Then: neg(ab) + ab ≡ 0 by inverse. b² + 0 + neg(a²) = b² - a²

    // Explicit transitive chains:
    // Chain for mul(ba,b) ≡ sub(b², ab):
    //   mul(ba,b) ≡ mul(b,ba) [commutative] ≡ add(b², mul(b,na)) [distributes]
    //   mul(b,na) ≡ neg(mul(b,a)) [neg_mul_right] ≡ neg(ab) [neg_congruence + commutative]
    //   → add(b², mul(b,na)) ≡ add(b², neg(ab)) = sub(b², ab)
    lemma_dts_neg_congruence(dts_mul(b, a), ab);
    lemma_dts_eqv_transitive(dts_mul(b, na), dts_neg(dts_mul(b, a)), dts_neg(ab));
    lemma_dts_add_congruence_right(b2, dts_mul(b, na), dts_neg(ab));
    lemma_dts_eqv_transitive(
        dts_mul(ba, b), dts_mul(b, ba),
        dts_add(b2, dts_mul(b, na)));
    lemma_dts_eqv_transitive(
        dts_mul(ba, b), dts_add(b2, dts_mul(b, na)),
        dts_add(b2, dts_neg(ab)));

    // Chain for mul(ba,a) ≡ sub(ab, a²):
    //   mul(ba,a) ≡ mul(a,ba) [commutative] ≡ add(mul(a,b), mul(a,na)) [distributes]
    //   mul(a,na) ≡ neg(a²) [neg_mul_right]
    //   → add(ab, mul(a,na)) ≡ add(ab, neg(a²)) = sub(ab, a²)
    lemma_dts_add_congruence_right(ab, dts_mul(a, na), dts_neg(a2));
    lemma_dts_eqv_transitive(
        dts_mul(ba, a), dts_mul(a, ba),
        dts_add(ab, dts_mul(a, na)));
    lemma_dts_eqv_transitive(
        dts_mul(ba, a), dts_add(ab, dts_mul(a, na)),
        dts_add(ab, dts_neg(a2)));

    // Combine: mul(ba,bpa) ≡ add(mul(ba,b), mul(ba,a))
    //        ≡ add(sub(b²,ab), sub(ab,a²)) [add_congruence from both chains]
    //        ≡ sub(b², a²) [sub_add_sub]
    lemma_dts_add_congruence_left(
        dts_mul(ba, b), dts_add(b2, dts_neg(ab)), dts_mul(ba, a));
    lemma_dts_add_congruence_right(
        dts_add(b2, dts_neg(ab)), dts_mul(ba, a), dts_add(ab, dts_neg(a2)));
    lemma_dts_eqv_transitive(
        dts_add(dts_mul(ba, b), dts_mul(ba, a)),
        dts_add(dts_add(b2, dts_neg(ab)), dts_mul(ba, a)),
        dts_add(dts_add(b2, dts_neg(ab)), dts_add(ab, dts_neg(a2))));
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_add_sub::<DynTowerSpec>(
        b2, ab, a2);
    // sub_add_sub: sub(b²,ab) + sub(ab,a²) ≡ sub(b²,a²)
    // = add(add(b²,neg(ab)), add(ab,neg(a²))) ≡ add(b²,neg(a²)) = sub(b²,a²)
    // Final: mul(ba,bpa) ≡ add(mul(ba,b),mul(ba,a)) ≡ add(sub(b²,ab),sub(ab,a²)) ≡ sub(b²,a²)
    lemma_dts_eqv_transitive(
        dts_mul(ba, bpa),
        dts_add(dts_mul(ba, b), dts_mul(ba, a)),
        dts_add(dts_add(b2, dts_neg(ab)), dts_add(ab, dts_neg(a2))));
    lemma_dts_eqv_transitive(
        dts_mul(ba, bpa),
        dts_add(dts_add(b2, dts_neg(ab)), dts_add(ab, dts_neg(a2))),
        dts_sub(b2, a2));
    // Symmetric: sub(b²,a²) ≡ mul(ba,bpa) → mul(ba,bpa) ≡ sub(b²,a²) already
    // But postcondition is eqv(sub(b²,a²), mul(ba,bpa))
    lemma_dts_eqv_symmetric(dts_mul(ba, bpa), dts_sub(b2, a2));
}

/// Multiplication associativity: mul(a, mul(b, c)) ≡ mul(mul(a, b), c).
/// Structural induction on DTS depth, 8 depth combinations.
pub proof fn lemma_dts_mul_associative(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec,
)
    requires
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
        dts_same_radicand(a, b), dts_same_radicand(b, c),
    ensures
        dts_eqv(dts_mul(a, dts_mul(b, c)), dts_mul(dts_mul(a, b), c)),
    decreases a, b, c,
{
    lemma_dts_same_radicand_transitive(a, b, c);
    match (a, b, c) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2), DynTowerSpec::Rat(r3)) => {
            Rational::axiom_mul_associative(r1, r2, r3);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Rat(_), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_mul_associative(DynTowerSpec::Rat(r), b, *re);
            lemma_dts_mul_associative(DynTowerSpec::Rat(r), b, *im);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(_)) => {
            lemma_dts_mul_associative(DynTowerSpec::Rat(r), *re, c);
            lemma_dts_mul_associative(DynTowerSpec::Rat(r), *im, c);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {
            lemma_dts_mul_associative(*re, b, c);
            lemma_dts_mul_associative(*im, b, c);
        }
        // ═══ REE: a=Rat, b=Ext, c=Ext — vacuous: same_radicand(Rat, Ext) = false ═══
        (DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _), DynTowerSpec::Ext(_, _, _)) => {
            // same_radicand(a, b) = same_radicand(Rat, Ext) = false by definition
            assert(!dts_same_radicand(a, b));
        }
        // ═══ ERE: a=Ext, b=Rat, c=Ext — vacuous: same_radicand(Rat, Ext) = false ═══
        (DynTowerSpec::Ext(_, _, _), DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _)) => {
            // same_radicand(b, c) = same_radicand(Rat, Ext) = false by definition
            assert(!dts_same_radicand(b, c));
        }
        // ═══ EER: a=Ext, b=Ext, c=Rat — vacuous: same_radicand(Ext, Rat) = false ═══
        (DynTowerSpec::Ext(_, _, _), DynTowerSpec::Ext(_, _, _), DynTowerSpec::Rat(_)) => {
            // same_radicand(b, c) = same_radicand(Ext, Rat) = false by definition
            assert(!dts_same_radicand(b, c));
        }
        // ═══ EEE — IH assoc calls here, then delegate to helper ═══
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _), DynTowerSpec::Ext(re3, im3, _)) => {
            // IH assoc on all 8 sub-component triples (decreases: sub-components < Ext)
            lemma_dts_mul_associative(*re1, *re2, *re3);
            lemma_dts_mul_associative(*re1, *re2, *im3);
            lemma_dts_mul_associative(*re1, *im2, *re3);
            lemma_dts_mul_associative(*re1, *im2, *im3);
            lemma_dts_mul_associative(*im1, *re2, *re3);
            lemma_dts_mul_associative(*im1, *re2, *im3);
            lemma_dts_mul_associative(*im1, *im2, *re3);
            lemma_dts_mul_associative(*im1, *im2, *im3);
            // Delegate rest to helper (no recursion, just chaining)
            lemma_dts_mul_associative_eee(*re1, *im1, *re2, *im2, *re3, *im3, *d);
        }
        _ => {}
    }
}

/// Helper for EEE case of mul_associative. Extracted for Z3 rlimit scalability.
proof fn lemma_dts_mul_associative_eee(
    a1: DynTowerSpec, a2: DynTowerSpec, b1: DynTowerSpec, b2: DynTowerSpec,
    c1: DynTowerSpec, c2: DynTowerSpec, dd: DynTowerSpec,
)
    requires
        dts_well_formed(DynTowerSpec::Ext(Box::new(a1), Box::new(a2), Box::new(dd))),
        dts_well_formed(DynTowerSpec::Ext(Box::new(b1), Box::new(b2), Box::new(dd))),
        dts_well_formed(DynTowerSpec::Ext(Box::new(c1), Box::new(c2), Box::new(dd))),
        dts_same_radicand(a1, b1), dts_same_radicand(a2, b2),
        dts_same_radicand(b1, c1), dts_same_radicand(b2, c2),
        // IH assoc results (passed from parent to avoid mutual recursion)
        dts_eqv(dts_mul(a1, dts_mul(b1, c1)), dts_mul(dts_mul(a1, b1), c1)),
        dts_eqv(dts_mul(a1, dts_mul(b1, c2)), dts_mul(dts_mul(a1, b1), c2)),
        dts_eqv(dts_mul(a1, dts_mul(b2, c1)), dts_mul(dts_mul(a1, b2), c1)),
        dts_eqv(dts_mul(a1, dts_mul(b2, c2)), dts_mul(dts_mul(a1, b2), c2)),
        dts_eqv(dts_mul(a2, dts_mul(b1, c1)), dts_mul(dts_mul(a2, b1), c1)),
        dts_eqv(dts_mul(a2, dts_mul(b1, c2)), dts_mul(dts_mul(a2, b1), c2)),
        dts_eqv(dts_mul(a2, dts_mul(b2, c1)), dts_mul(dts_mul(a2, b2), c1)),
        dts_eqv(dts_mul(a2, dts_mul(b2, c2)), dts_mul(dts_mul(a2, b2), c2)),
    ensures
        dts_eqv(
            dts_mul(
                DynTowerSpec::Ext(Box::new(a1), Box::new(a2), Box::new(dd)),
                dts_mul(
                    DynTowerSpec::Ext(Box::new(b1), Box::new(b2), Box::new(dd)),
                    DynTowerSpec::Ext(Box::new(c1), Box::new(c2), Box::new(dd)))),
            dts_mul(
                dts_mul(
                    DynTowerSpec::Ext(Box::new(a1), Box::new(a2), Box::new(dd)),
                    DynTowerSpec::Ext(Box::new(b1), Box::new(b2), Box::new(dd))),
                DynTowerSpec::Ext(Box::new(c1), Box::new(c2), Box::new(dd)))),
    decreases a1, b1, c1,
{
            // ── Infrastructure: derive cross same_radicand ──
            // Direct from preconditions: a1~b1, a2~b2, b1~c1, b2~c2
            // From well_formed: a1~a2, a1~d, b1~b2, b1~d, c1~c2, c1~d
            // Derived chains:
            lemma_dts_same_radicand_transitive(b1, c1, c2); // b1~c2
            lemma_dts_same_radicand_transitive(a1, a2, b2); // a1~b2 (a1~a2, a2~b2)
            lemma_dts_same_radicand_symmetric(a1, b1);
            lemma_dts_same_radicand_transitive(b1, a1, a2); // b1~a2
            lemma_dts_same_radicand_symmetric(b1, b2);
            lemma_dts_same_radicand_symmetric(c1, c2);
            lemma_dts_same_radicand_transitive(b2, c2, c1); // b2~c1
            lemma_dts_same_radicand_transitive(a1, b1, c1); // a1~c1
            lemma_dts_same_radicand_transitive(a1, c1, c2); // a1~c2
            lemma_dts_same_radicand_transitive(a2, b2, c2); // a2~c2
            lemma_dts_same_radicand_symmetric(a1, a2);
            lemma_dts_same_radicand_transitive(a2, a1, c1); // a2~c1
            lemma_dts_same_radicand_symmetric(b1, a2);
            lemma_dts_same_radicand_transitive(a2, b1, c1); // a2~c1 via b1 too
            lemma_dts_same_radicand_symmetric(a1, dd);
            lemma_dts_same_radicand_transitive(dd, a1, a2);
            lemma_dts_same_radicand_transitive(dd, a1, b1);
            lemma_dts_same_radicand_transitive(dd, a1, b2);
            lemma_dts_same_radicand_transitive(dd, a1, c1);
            lemma_dts_same_radicand_transitive(dd, a1, c2);
            // IH assoc results are in context from parent caller
            // ── mul_closed for all needed products ──
            lemma_dts_mul_closed(a1, b1);
            lemma_dts_mul_closed(a2, b2);
            lemma_dts_mul_closed(a1, b2);
            lemma_dts_mul_closed(a2, b1);
            lemma_dts_mul_closed(b1, c1);
            lemma_dts_mul_closed(b1, c2);
            lemma_dts_mul_closed(b2, c1);
            lemma_dts_mul_closed(b2, c2);
            lemma_dts_same_radicand_symmetric(b2, dts_mul(b2, c2));
            lemma_dts_same_radicand_transitive(dd, b2, dts_mul(b2, c2));
            lemma_dts_mul_closed(dd, dts_mul(b2, c2));
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, b2));
            lemma_dts_same_radicand_transitive(dd, a2, dts_mul(a2, b2));
            lemma_dts_mul_closed(dd, dts_mul(a2, b2));
            // same_radicand chains for distributes preconditions
            lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, c1));
            lemma_dts_same_radicand_transitive(a1, b1, dts_mul(b1, c1));
            lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, c2));
            lemma_dts_same_radicand_transitive(a1, b1, dts_mul(b1, c2));
            lemma_dts_same_radicand_symmetric(b2, dts_mul(b2, c1));
            lemma_dts_same_radicand_transitive(a1, b2, dts_mul(b2, c1));
            lemma_dts_same_radicand_symmetric(b2, dts_mul(b2, c2));
            lemma_dts_same_radicand_transitive(a1, b2, dts_mul(b2, c2));
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_same_radicand_transitive(dts_mul(b1, c1), b1, dd);
            lemma_dts_same_radicand_transitive(dts_mul(b1, c1), dd, dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_same_radicand_transitive(dts_mul(b1, c2), b1, b2);
            lemma_dts_same_radicand_transitive(dts_mul(b1, c2), b2, dts_mul(b2, c1));
            lemma_dts_same_radicand_symmetric(a2, b1);
            lemma_dts_same_radicand_transitive(a2, b1, dts_mul(b1, c1));
            lemma_dts_same_radicand_transitive(a2, b1, dts_mul(b1, c2));
            // ── IH distributes on sub-component triples ──
            lemma_dts_mul_distributes_left(a1, dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_mul_distributes_left(a2, dts_mul(b1, c2), dts_mul(b2, c1));
            lemma_dts_mul_distributes_left(a1, dts_mul(b1, c2), dts_mul(b2, c1));
            lemma_dts_mul_distributes_left(a2, dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, b1));
            lemma_dts_same_radicand_transitive(dts_mul(a1, b1), a1, dd);
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(a2, b2)));
            lemma_dts_same_radicand_transitive(dts_mul(a1, b1), dd, dts_mul(dd, dts_mul(a2, b2)));
            lemma_dts_add_closed(dts_mul(a1, b1), dts_mul(dd, dts_mul(a2, b2)));
            lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, b2));
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, b1));
            lemma_dts_same_radicand_transitive(b1, a2, dts_mul(a2, b1));
            lemma_dts_same_radicand_transitive(dts_mul(a1, b2), a1, b1);
            lemma_dts_same_radicand_transitive(dts_mul(a1, b2), b1, dts_mul(a2, b1));
            lemma_dts_add_closed(dts_mul(a1, b2), dts_mul(a2, b1));
            let re_ab = dts_add(dts_mul(a1, b1), dts_mul(dd, dts_mul(a2, b2)));
            let im_ab = dts_add(dts_mul(a1, b2), dts_mul(a2, b1));
            // RHS distributes: re_ab*c1 + d*im_ab*c2 and re_ab*c2 + im_ab*c1
            lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, b1));
            lemma_dts_same_radicand_transitive(dts_mul(a1, b1), a1, c1);
            lemma_dts_same_radicand_transitive(dts_mul(a1, b1), a1, c2);
            lemma_dts_same_radicand_symmetric(dts_mul(a1, b1), re_ab);
            lemma_dts_same_radicand_transitive(re_ab, dts_mul(a1, b1), c1);
            lemma_dts_same_radicand_transitive(re_ab, dts_mul(a1, b1), c2);
            lemma_dts_mul_distributes_left(re_ab, dts_mul(a1, b1), dts_mul(dd, dts_mul(a2, b2)));
            // Wait, that's wrong — distributes_left(X, Y, Z) gives X*(Y+Z) = X*Y + X*Z
            // But I want (Y+Z)*c1 = Y*c1 + Z*c1, i.e., right distributes.
            // Use commut: (re_ab)*c1 ≡ c1*(re_ab) = c1*(a1b1+da2b2) ≡ c1*a1b1 + c1*da2b2
            // Then commut each back.
            // Actually, I already have distributes_left. For right distributes I can use:
            // mul(add(X,Y), Z) by commut → mul(Z, add(X,Y)) by distributes → add(mul(Z,X), mul(Z,Y))
            // then commut each term back. But that's a LOT of boilerplate.
            // Alternatively: the Ext×Ext mul definition STRUCTURALLY gives the re and im components.
            // So mul(Ext(re_ab, im_ab, d), Ext(c1, c2, d)):
            //   re = add(mul(re_ab, c1), mul(d, mul(im_ab, c2)))
            //   im = add(mul(re_ab, c2), mul(im_ab, c1))
            // These are the structural terms. I need to show they're eqv to the LHS terms.
            //
            // For the re component of RHS:
            //   add(mul(re_ab, c1), mul(d, mul(im_ab, c2)))
            //   = add(mul(add(a1b1, da2b2), c1), mul(d, mul(add(a1b2, a2b1), c2)))
            //
            // This is a HUGE expansion. Let me use a different strategy:
            // provide IH assoc + distributes facts and let Z3 handle the structural unfolding.
            // The structural dts_mul and dts_add definitions should unfold, and Z3 should
            // be able to match the terms with the IH facts.
            //
            // Key: dts_eqv for Ext checks component-wise. So Z3 needs to verify:
            //   eqv(LHS_re, RHS_re) && eqv(LHS_im, RHS_im)
            // where each is built from sub-component operations.
            //
            // With IH assoc and distributes already established, Z3 should propagate.
            // But the function is large and Z3 might struggle. Let me try and see.

            // ── d chains for LHS ──
            // d*(a2*(b1c2+b2c1)) ≡ d*(a2*b1c2 + a2*b2c1): congruence from distributes IH
            lemma_dts_mul_congruence_right(
                dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1))),
                dts_add(dts_mul(a2, dts_mul(b1, c2)), dts_mul(a2, dts_mul(b2, c1))),
                dd);
            // d*(a2*b1c2 + a2*b2c1) ≡ d*a2*b1c2 + d*a2*b2c1
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, dts_mul(b1, c2)));
            lemma_dts_mul_closed(a2, dts_mul(b1, c2));
            lemma_dts_mul_closed(a2, dts_mul(b2, c1));
            lemma_dts_same_radicand_transitive(
                dts_mul(a2, dts_mul(b1, c2)), a2, dts_mul(a2, dts_mul(b2, c1)));
            lemma_dts_same_radicand_symmetric(dd, dts_mul(a2, dts_mul(b1, c2)));
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, dts_mul(b2, c1)));
            lemma_dts_same_radicand_transitive(dd, dts_mul(a2, dts_mul(b1, c2)),
                dts_mul(a2, dts_mul(b2, c1)));
            lemma_dts_mul_distributes_left(dd,
                dts_mul(a2, dts_mul(b1, c2)), dts_mul(a2, dts_mul(b2, c1)));
            lemma_dts_eqv_transitive(
                dts_mul(dd, dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1)))),
                dts_mul(dd, dts_add(dts_mul(a2, dts_mul(b1, c2)), dts_mul(a2, dts_mul(b2, c1)))),
                dts_add(dts_mul(dd, dts_mul(a2, dts_mul(b1, c2))), dts_mul(dd, dts_mul(a2, dts_mul(b2, c1)))));

            // Similarly for a1*(b1c1+db2c2):
            lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, c1));
            lemma_dts_same_radicand_transitive(dts_mul(b1, c1), b1, dd);
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_same_radicand_transitive(dts_mul(b1, c1), dd, dts_mul(dd, dts_mul(b2, c2)));
            lemma_dts_same_radicand_symmetric(a1, dts_mul(b1, c1));
            lemma_dts_same_radicand_transitive(a1, dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)));

            // LHS re = a1*(b1c1+db2c2) + d*a2*(b1c2+b2c1)
            // Expand a1*(b1c1+db2c2) using distributes:
            lemma_dts_add_congruence_left(
                dts_mul(a1, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)))),
                dts_add(dts_mul(a1, dts_mul(b1, c1)), dts_mul(a1, dts_mul(dd, dts_mul(b2, c2)))),
                dts_mul(dd, dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1)))));
            // Expand d*a2*(b1c2+b2c1) (already done above)
            lemma_dts_add_congruence_right(
                dts_add(dts_mul(a1, dts_mul(b1, c1)), dts_mul(a1, dts_mul(dd, dts_mul(b2, c2)))),
                dts_mul(dd, dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1)))),
                dts_add(dts_mul(dd, dts_mul(a2, dts_mul(b1, c2))), dts_mul(dd, dts_mul(a2, dts_mul(b2, c1)))));

            // LHS re ≡ (T1+T2) + (T3+T4) where:
            let t1 = dts_mul(a1, dts_mul(b1, c1));
            let t2 = dts_mul(a1, dts_mul(dd, dts_mul(b2, c2)));
            let t3 = dts_mul(dd, dts_mul(a2, dts_mul(b1, c2)));
            let t4 = dts_mul(dd, dts_mul(a2, dts_mul(b2, c1)));
            let lhs_re_expanded = dts_add(dts_add(t1, t2), dts_add(t3, t4));

            // Chain LHS_re to lhs_re_expanded
            let lhs_re = dts_add(
                dts_mul(a1, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)))),
                dts_mul(dd, dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1)))));
            lemma_dts_eqv_transitive(lhs_re,
                dts_add(
                    dts_add(t1, t2),
                    dts_mul(dd, dts_mul(a2, dts_add(dts_mul(b1, c2), dts_mul(b2, c1))))),
                lhs_re_expanded);

            // ── Now match terms: T1≡U1, T2≡U3, T3≡U4, T4≡U2 ──
            // U1 = (a1*b1)*c1, U2 = (d*(a2*b2))*c1, U3 = d*((a1*b2)*c2), U4 = d*((a2*b1)*c2)
            let u1 = dts_mul(dts_mul(a1, b1), c1);
            let u2 = dts_mul(dts_mul(dd, dts_mul(a2, b2)), c1);
            let u3 = dts_mul(dd, dts_mul(dts_mul(a1, b2), c2));
            let u4 = dts_mul(dd, dts_mul(dts_mul(a2, b1), c2));

            // T1 ≡ U1: a1*(b1*c1) ≡ (a1*b1)*c1 — direct IH assoc ✓

            // T2 ≡ U3: a1*(d*(b2*c2)) ≡ d*((a1*b2)*c2)
            // Chain: a1*(d*(b2*c2)) →[IH assoc]→ (a1*d)*(b2*c2) →[commut a1,d + congr]→
            //        (d*a1)*(b2*c2) →[IH assoc rev]→ d*(a1*(b2*c2)) →[congr + IH assoc]→ d*((a1*b2)*c2)
            lemma_dts_mul_associative(a1, dd, dts_mul(b2, c2));
            lemma_dts_mul_commutative(a1, dd);
            lemma_dts_mul_closed(a1, dd);
            lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, dd));
            lemma_dts_same_radicand_transitive(dts_mul(a1, dd), a1, dts_mul(b2, c2));
            lemma_dts_mul_congruence_left(dts_mul(a1, dd), dts_mul(dd, a1), dts_mul(b2, c2));
            lemma_dts_eqv_transitive(t2, dts_mul(dts_mul(a1, dd), dts_mul(b2, c2)),
                dts_mul(dts_mul(dd, a1), dts_mul(b2, c2)));
            lemma_dts_mul_closed(dd, a1);
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, a1));
            lemma_dts_same_radicand_transitive(dts_mul(dd, a1), dd, dts_mul(b2, c2));
            lemma_dts_mul_associative(dd, a1, dts_mul(b2, c2));
            lemma_dts_eqv_symmetric(dts_mul(dd, dts_mul(a1, dts_mul(b2, c2))),
                dts_mul(dts_mul(dd, a1), dts_mul(b2, c2)));
            lemma_dts_eqv_transitive(t2, dts_mul(dts_mul(dd, a1), dts_mul(b2, c2)),
                dts_mul(dd, dts_mul(a1, dts_mul(b2, c2))));
            // d*(a1*(b2*c2)) →[congr + IH assoc(a1,b2,c2)]→ d*((a1*b2)*c2) = U3
            lemma_dts_mul_congruence_right(dts_mul(a1, dts_mul(b2, c2)), dts_mul(dts_mul(a1, b2), c2), dd);
            lemma_dts_eqv_transitive(t2, dts_mul(dd, dts_mul(a1, dts_mul(b2, c2))), u3);

            // T3 ≡ U4: d*(a2*(b1*c2)) ≡ d*((a2*b1)*c2) — congr + IH assoc ✓
            lemma_dts_mul_congruence_right(dts_mul(a2, dts_mul(b1, c2)), dts_mul(dts_mul(a2, b1), c2), dd);

            // T4 ≡ U2: d*(a2*(b2*c1)) ≡ (d*(a2*b2))*c1
            // Chain: d*(a2*(b2*c1)) →[congr + IH assoc(a2,b2,c1)]→ d*((a2*b2)*c1)
            //        →[IH assoc(d,a2*b2,c1)]→ (d*(a2*b2))*c1 = U2
            lemma_dts_mul_congruence_right(dts_mul(a2, dts_mul(b2, c1)), dts_mul(dts_mul(a2, b2), c1), dd);
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, b2));
            lemma_dts_same_radicand_transitive(dd, a2, dts_mul(a2, b2));
            lemma_dts_same_radicand_symmetric(a2, c1);
            lemma_dts_same_radicand_transitive(dts_mul(a2, b2), a2, c1);
            lemma_dts_mul_associative(dd, dts_mul(a2, b2), c1);
            lemma_dts_eqv_symmetric(dts_mul(dd, dts_mul(dts_mul(a2, b2), c1)),
                dts_mul(dts_mul(dd, dts_mul(a2, b2)), c1));
            lemma_dts_eqv_transitive(t4, dts_mul(dd, dts_mul(dts_mul(a2, b2), c1)), u2);

            // ── Rearrange: (T1+T2)+(T3+T4) ≡ (U1+U3)+(U4+U2) → (U1+U2)+(U3+U4) ──
            // Step 1: congruence from Ti ≡ Uj
            lemma_dts_add_congruence_left(t1, u1, t2);
            lemma_dts_add_congruence_right(u1, t2, u3);
            lemma_dts_add_congruence_left(t3, u4, t4);
            lemma_dts_add_congruence_right(u4, t4, u2);
            // (T1+T2) ≡ (U1+U3), (T3+T4) ≡ (U4+U2)
            lemma_dts_eqv_transitive(dts_add(t1, t2), dts_add(u1, t2), dts_add(u1, u3));
            lemma_dts_eqv_transitive(dts_add(t3, t4), dts_add(u4, t4), dts_add(u4, u2));
            // lhs_re_expanded = (T1+T2)+(T3+T4) ≡ (U1+U3)+(U4+U2)
            lemma_dts_add_congruence_left(dts_add(t1, t2), dts_add(u1, u3), dts_add(t3, t4));
            lemma_dts_add_congruence_right(dts_add(u1, u3), dts_add(t3, t4), dts_add(u4, u2));
            lemma_dts_eqv_transitive(lhs_re_expanded,
                dts_add(dts_add(u1, u3), dts_add(t3, t4)),
                dts_add(dts_add(u1, u3), dts_add(u4, u2)));

            // Step 2: commut second pair (U4+U2) → (U2+U4)
            lemma_dts_mul_closed(dts_mul(dd, dts_mul(a2, b2)), c1);
            lemma_dts_mul_closed(dts_mul(a2, b1), c2);
            lemma_dts_mul_closed(dd, dts_mul(dts_mul(a2, b1), c2));
            lemma_dts_mul_closed(dts_mul(a1, b2), c2);
            lemma_dts_mul_closed(dd, dts_mul(dts_mul(a1, b2), c2));
            // same_radicand for u2, u4 exchange
            lemma_dts_same_radicand_symmetric(dts_mul(a1, b1), u1);
            lemma_dts_same_radicand_transitive(u1, dts_mul(a1, b1), dd);
            lemma_dts_same_radicand_transitive(u1, dd, u3);
            lemma_dts_same_radicand_transitive(u1, dd, u2);
            lemma_dts_same_radicand_transitive(u1, dd, u4);
            lemma_dts_same_radicand_symmetric(u1, u4);
            lemma_dts_same_radicand_transitive(u4, u1, u2);
            DynTowerSpec::axiom_add_commutative(u4, u2);
            lemma_dts_add_congruence_right(dts_add(u1, u3), dts_add(u4, u2), dts_add(u2, u4));
            lemma_dts_eqv_transitive(
                dts_add(dts_add(u1, u3), dts_add(u4, u2)),
                dts_add(dts_add(u1, u3), dts_add(u2, u4)),
                dts_add(dts_add(u1, u3), dts_add(u2, u4))); // identity step

            // Step 3: exchange (U1+U3)+(U2+U4) → (U1+U2)+(U3+U4)
            lemma_dts_same_radicand_symmetric(u1, u3);
            lemma_dts_same_radicand_transitive(u3, u1, u2);
            lemma_dts_same_radicand_symmetric(u1, u2);
            lemma_dts_same_radicand_transitive(u2, u1, u4);
            lemma_dts_add_exchange(u1, u3, u2, u4);

            // Chain lhs_re_expanded ≡ ... ≡ (U1+U2)+(U3+U4)
            let rhs_re = dts_add(dts_add(u1, u2), dts_add(u3, u4));
            lemma_dts_eqv_transitive(lhs_re_expanded,
                dts_add(dts_add(u1, u3), dts_add(u4, u2)),
                dts_add(dts_add(u1, u3), dts_add(u2, u4)));
            lemma_dts_eqv_transitive(lhs_re_expanded,
                dts_add(dts_add(u1, u3), dts_add(u2, u4)),
                rhs_re);

            // Full re chain: lhs_re ≡ lhs_re_expanded ≡ rhs_re
            lemma_dts_eqv_transitive(lhs_re, lhs_re_expanded, rhs_re);

            // ══ Im component: same structure ══
            // LHS im = a1*(b1c2+b2c1) + a2*(b1c1+db2c2)
            // Expanding: (a1*(b1*c2) + a1*(b2*c1)) + (a2*(b1*c1) + a2*(d*(b2*c2)))
            // RHS im = re_ab*c2 + im_ab*c1
            // = (a1b1+da2b2)*c2 + (a1b2+a2b1)*c1
            // Struct: add(mul(re_ab, c2), mul(im_ab, c1))
            // Expanding: ((a1*b1)*c2 + (d*(a2*b2))*c2) + ((a1*b2)*c1 + (a2*b1)*c1)
            let s1 = dts_mul(a1, dts_mul(b1, c2));
            let s2 = dts_mul(a1, dts_mul(b2, c1));
            let s3 = dts_mul(a2, dts_mul(b1, c1));
            let s4 = dts_mul(a2, dts_mul(dd, dts_mul(b2, c2)));
            let v1 = dts_mul(dts_mul(a1, b1), c2);
            let v2 = dts_mul(dts_mul(dd, dts_mul(a2, b2)), c2);
            let v3 = dts_mul(dts_mul(a1, b2), c1);
            let v4 = dts_mul(dts_mul(a2, b1), c1);

            // S1≡V1: IH assoc(a1,b1,c2) ✓ (already called)
            // S2≡V3: IH assoc(a1,b2,c1) ✓
            // S3≡V4: IH assoc(a2,b1,c1) ✓
            // S4≡V2: a2*(d*(b2*c2)) ≡ (d*(a2*b2))*c2 — same chain as T4≡U2 but with c2
            lemma_dts_mul_congruence_right(dts_mul(a2, dts_mul(b2, c2)), dts_mul(dts_mul(a2, b2), c2), dd);
            lemma_dts_mul_associative(dd, dts_mul(a2, b2), c2);
            lemma_dts_eqv_symmetric(dts_mul(dd, dts_mul(dts_mul(a2, b2), c2)),
                dts_mul(dts_mul(dd, dts_mul(a2, b2)), c2));
            // s4 = a2*(d*(b2*c2)). Need chain: same as T2≡U3 pattern but with a2 instead of a1
            lemma_dts_mul_associative(a2, dd, dts_mul(b2, c2));
            lemma_dts_mul_commutative(a2, dd);
            lemma_dts_mul_closed(a2, dd);
            lemma_dts_same_radicand_symmetric(a2, dts_mul(a2, dd));
            lemma_dts_same_radicand_transitive(dts_mul(a2, dd), a2, dts_mul(b2, c2));
            lemma_dts_mul_congruence_left(dts_mul(a2, dd), dts_mul(dd, a2), dts_mul(b2, c2));
            lemma_dts_eqv_transitive(s4, dts_mul(dts_mul(a2, dd), dts_mul(b2, c2)),
                dts_mul(dts_mul(dd, a2), dts_mul(b2, c2)));
            lemma_dts_mul_closed(dd, a2);
            lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, a2));
            lemma_dts_same_radicand_transitive(dts_mul(dd, a2), dd, dts_mul(b2, c2));
            lemma_dts_mul_associative(dd, a2, dts_mul(b2, c2));
            lemma_dts_eqv_symmetric(dts_mul(dd, dts_mul(a2, dts_mul(b2, c2))),
                dts_mul(dts_mul(dd, a2), dts_mul(b2, c2)));
            lemma_dts_eqv_transitive(s4, dts_mul(dts_mul(dd, a2), dts_mul(b2, c2)),
                dts_mul(dd, dts_mul(a2, dts_mul(b2, c2))));
            lemma_dts_eqv_transitive(s4, dts_mul(dd, dts_mul(a2, dts_mul(b2, c2))),
                dts_mul(dd, dts_mul(dts_mul(a2, b2), c2)));
            lemma_dts_eqv_transitive(s4, dts_mul(dd, dts_mul(dts_mul(a2, b2), c2)), v2);

            // Expand LHS im and chain to (S1+S2)+(S3+S4)
            lemma_dts_add_congruence_left(
                dts_mul(a1, dts_add(dts_mul(b1, c2), dts_mul(b2, c1))),
                dts_add(s1, s2),
                dts_mul(a2, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)))));
            lemma_dts_add_congruence_right(
                dts_add(s1, s2),
                dts_mul(a2, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)))),
                dts_add(s3, s4));
            let lhs_im = dts_add(
                dts_mul(a1, dts_add(dts_mul(b1, c2), dts_mul(b2, c1))),
                dts_mul(a2, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2)))));
            let lhs_im_expanded = dts_add(dts_add(s1, s2), dts_add(s3, s4));
            lemma_dts_eqv_transitive(lhs_im,
                dts_add(dts_add(s1, s2),
                    dts_mul(a2, dts_add(dts_mul(b1, c1), dts_mul(dd, dts_mul(b2, c2))))),
                lhs_im_expanded);

            // Rearrange im: (S1+S2)+(S3+S4) → (V1+V3)+(V4+V2) → (V1+V2)+(V3+V4)
            lemma_dts_add_congruence_left(s1, v1, s2);
            lemma_dts_add_congruence_right(v1, s2, v3);
            lemma_dts_add_congruence_left(s3, v4, s4);
            lemma_dts_add_congruence_right(v4, s4, v2);
            lemma_dts_eqv_transitive(dts_add(s1, s2), dts_add(v1, s2), dts_add(v1, v3));
            lemma_dts_eqv_transitive(dts_add(s3, s4), dts_add(v4, s4), dts_add(v4, v2));
            lemma_dts_add_congruence_left(dts_add(s1, s2), dts_add(v1, v3), dts_add(s3, s4));
            lemma_dts_add_congruence_right(dts_add(v1, v3), dts_add(s3, s4), dts_add(v4, v2));
            lemma_dts_eqv_transitive(lhs_im_expanded,
                dts_add(dts_add(v1, v3), dts_add(s3, s4)),
                dts_add(dts_add(v1, v3), dts_add(v4, v2)));

            // Commut (V4+V2)→(V2+V4) and exchange
            lemma_dts_mul_closed(dts_mul(dd, dts_mul(a2, b2)), c2);
            lemma_dts_mul_closed(dts_mul(a1, b2), c1);
            lemma_dts_mul_closed(dts_mul(a2, b1), c1);
            lemma_dts_same_radicand_symmetric(dts_mul(a1, b1), v1);
            lemma_dts_same_radicand_transitive(v1, dts_mul(a1, b1), dd);
            lemma_dts_same_radicand_transitive(v1, dd, v2);
            lemma_dts_same_radicand_transitive(v1, dd, v3);
            lemma_dts_same_radicand_transitive(v1, dd, v4);
            lemma_dts_same_radicand_symmetric(v1, v4);
            lemma_dts_same_radicand_transitive(v4, v1, v2);
            DynTowerSpec::axiom_add_commutative(v4, v2);
            lemma_dts_add_congruence_right(dts_add(v1, v3), dts_add(v4, v2), dts_add(v2, v4));
            lemma_dts_same_radicand_symmetric(v1, v3);
            lemma_dts_same_radicand_transitive(v3, v1, v2);
            lemma_dts_same_radicand_symmetric(v1, v2);
            lemma_dts_same_radicand_transitive(v2, v1, v4);
            lemma_dts_add_exchange(v1, v3, v2, v4);
            let rhs_im = dts_add(dts_add(v1, v2), dts_add(v3, v4));
            lemma_dts_eqv_transitive(
                dts_add(dts_add(v1, v3), dts_add(v4, v2)),
                dts_add(dts_add(v1, v3), dts_add(v2, v4)),
                rhs_im);
            lemma_dts_eqv_transitive(lhs_im_expanded,
                dts_add(dts_add(v1, v3), dts_add(v4, v2)),
                rhs_im);
            lemma_dts_eqv_transitive(lhs_im, lhs_im_expanded, rhs_im);
}

/// a·(b-c) ≡ a·b - a·c. Distributes mul over sub.
pub proof fn lemma_dts_mul_distributes_over_sub(a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec)
    requires
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
        dts_same_radicand(a, b), dts_same_radicand(a, c),
    ensures
        dts_eqv(dts_mul(a, dts_sub(b, c)),
                dts_sub(dts_mul(a, b), dts_mul(a, c))),
{
    lemma_dts_neg_well_formed(c);
    lemma_dts_same_radicand_neg(c);
    lemma_dts_same_radicand_symmetric(a, c);
    lemma_dts_same_radicand_transitive(a, c, dts_neg(c));
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, dts_neg(c));
    lemma_dts_mul_distributes_left(a, b, dts_neg(c));
    lemma_dts_neg_mul_right(a, c);
    lemma_dts_add_congruence_right(dts_mul(a, b), dts_mul(a, dts_neg(c)), dts_neg(dts_mul(a, c)));
    DynTowerSpec::axiom_sub_is_add_neg(dts_mul(a, b), dts_mul(a, c));
    lemma_dts_eqv_symmetric(dts_sub(dts_mul(a, b), dts_mul(a, c)),
        dts_add(dts_mul(a, b), dts_neg(dts_mul(a, c))));
    lemma_dts_eqv_transitive(
        dts_mul(a, dts_sub(b, c)),
        dts_add(dts_mul(a, b), dts_mul(a, dts_neg(c))),
        dts_add(dts_mul(a, b), dts_neg(dts_mul(a, c))));
    lemma_dts_eqv_transitive(
        dts_mul(a, dts_sub(b, c)),
        dts_add(dts_mul(a, b), dts_neg(dts_mul(a, c))),
        dts_sub(dts_mul(a, b), dts_mul(a, c)));
}

/// (a-b)·c ≡ a·c - b·c. Distributes sub-mul on the right.
pub proof fn lemma_dts_sub_mul_right(a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec)
    requires
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
        dts_same_radicand(a, b), dts_same_radicand(a, c),
    ensures
        dts_eqv(dts_mul(dts_sub(a, b), c),
                dts_sub(dts_mul(a, c), dts_mul(b, c))),
{
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, c);
    lemma_dts_neg_well_formed(b);
    lemma_dts_same_radicand_neg(b);
    lemma_dts_same_radicand_transitive(a, b, dts_neg(b));
    lemma_dts_add_closed(a, dts_neg(b));
    lemma_dts_same_radicand_symmetric(a, dts_sub(a, b));
    lemma_dts_same_radicand_transitive(dts_sub(a, b), a, c);
    lemma_dts_mul_commutative(dts_sub(a, b), c);
    lemma_dts_same_radicand_symmetric(a, c);
    lemma_dts_same_radicand_transitive(c, a, b);
    lemma_dts_mul_distributes_over_sub(c, a, b);
    lemma_dts_mul_commutative(c, a);
    lemma_dts_mul_commutative(c, b);
    // same_radicand for sub_congruence_both
    lemma_dts_mul_closed(c, a);
    lemma_dts_mul_closed(a, c);
    lemma_dts_mul_closed(c, b);
    lemma_dts_mul_closed(b, c);
    lemma_dts_same_radicand_symmetric(a, dts_mul(a, c));
    lemma_dts_same_radicand_transitive(c, a, dts_mul(a, c));
    lemma_dts_same_radicand_symmetric(c, dts_mul(c, a));
    lemma_dts_same_radicand_transitive(dts_mul(c, a), c, dts_mul(a, c));
    lemma_dts_same_radicand_symmetric(b, dts_mul(b, c));
    lemma_dts_same_radicand_transitive(c, b, dts_mul(b, c));
    lemma_dts_same_radicand_symmetric(c, dts_mul(c, b));
    lemma_dts_same_radicand_transitive(dts_mul(c, b), c, dts_mul(b, c));
    lemma_dts_sub_congruence_both(dts_mul(c, a), dts_mul(c, b), dts_mul(a, c), dts_mul(b, c));
    lemma_dts_eqv_transitive(
        dts_mul(dts_sub(a, b), c), dts_mul(c, dts_sub(a, b)),
        dts_sub(dts_mul(c, a), dts_mul(c, b)));
    lemma_dts_eqv_transitive(
        dts_mul(dts_sub(a, b), c),
        dts_sub(dts_mul(c, a), dts_mul(c, b)),
        dts_sub(dts_mul(a, c), dts_mul(b, c)));
}

// TODO: lemma_dts_mul_associative — mul(a, mul(b, c)) ≡ mul(mul(a, b), c)
// Prerequisite for: square_mul, four_commute, norm_mul, all remaining nonneg_mul cases
// ~300-500 lines, structural induction on DTS depth, 8 depth combinations

/// Square-le-square at fuel level: 0 ≤ a ≤ b → a² ≤ b².
/// Uses difference_of_squares: b²-a² = (b-a)(b+a), both factors nonneg.
/// Requires nonneg_mul IH (mutually recursive).
pub proof fn lemma_dts_square_le_square_fuel(
    a: DynTowerSpec, b: DynTowerSpec, fuel: nat,
)
    requires
        fuel >= dts_depth(a) + 1, fuel >= dts_depth(b) + 1,
        dts_well_formed(a), dts_well_formed(b), dts_same_radicand(a, b),
        dts_nonneg_radicands(a), dts_nonneg_radicands(b),
        dts_nonneg_fuel(a, fuel),
        dts_nonneg_fuel(dts_sub(b, a), fuel),
    ensures
        dts_nonneg_fuel(dts_sub(dts_mul(b, b), dts_mul(a, a)), fuel),
    decreases fuel,
{
    // Setup: neg(a) infrastructure
    lemma_dts_neg_well_formed(a);
    lemma_dts_same_radicand_neg(a);
    lemma_dts_same_radicand_reflexive(a);
    lemma_dts_same_radicand_reflexive(b);
    lemma_dts_same_radicand_symmetric(a, dts_neg(a));
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, dts_neg(a));
    lemma_dts_add_closed(b, dts_neg(a));
    lemma_dts_nonneg_radicands_neg(a);
    lemma_dts_nonneg_radicands_add(b, dts_neg(a));
    lemma_dts_depth_neg(a);
    lemma_dts_depth_add_le(b, dts_neg(a));
    lemma_dts_difference_of_squares(a, b);
    // nonneg(b): from nonneg(a) + nonneg(b-a) → nonneg(a + (b-a))
    // a + (b-a) = a + sub(b,a) = a + add(b, neg(a)) ≡ b by additive algebra
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<DynTowerSpec>(b, a);
    // (b + a) - a ≡ b. Hmm wait, add_then_sub gives (a+b)-b ≡ a. I want a+(b-a) ≡ b.
    // Actually: a + sub(b,a) = a + (b-a). By commutative: (b-a) + a.
    // sub_add_cancel: sub(b,a).add(a) ≡ b. This is the right one.
    // But I need nonneg(b) from nonneg(a) + nonneg(sub(b,a)).
    // sum = add(a, sub(b,a)) ≡ b [by sub then add cancel]
    // nonneg(sum) by nonneg_add IH, then nonneg(b) by congruence.
    lemma_dts_same_radicand_symmetric(b, dts_sub(b, a));
    lemma_dts_same_radicand_transitive(a, b, dts_sub(b, a));
    lemma_dts_same_radicand_symmetric(a, dts_sub(b, a));
    lemma_dts_nonneg_add_closed_fuel(a, dts_sub(b, a), fuel);
    // nonneg(add(a, sub(b,a)))
    // add(a, sub(b,a)) ≡ b: use additive group lemma
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<DynTowerSpec>(b, a);
    // sub(b,a).add(a) ≡ b → add(sub(b,a), a) ≡ b
    DynTowerSpec::axiom_add_commutative(a, dts_sub(b, a));
    lemma_dts_eqv_transitive(dts_add(a, dts_sub(b, a)), dts_add(dts_sub(b, a), a), b);
    // nonneg(add(a, sub(b,a))) → nonneg(b) by congruence
    // Need same_radicand for congruence
    lemma_dts_add_closed(a, dts_sub(b, a));
    lemma_dts_same_radicand_symmetric(a, dts_add(a, dts_sub(b, a)));
    lemma_dts_same_radicand_transitive(dts_add(a, dts_sub(b, a)), a, b);
    lemma_dts_nonneg_fuel_congruence(dts_add(a, dts_sub(b, a)), b, fuel);
    // Now nonneg(b). So nonneg(add(b,a)) by nonneg_add IH.
    lemma_dts_nonneg_add_closed_fuel(b, a, fuel);
    // nonneg(sub(b,a)) AND nonneg(add(b,a)) → nonneg(mul(sub(b,a), add(b,a))) by nonneg_mul IH
    lemma_dts_add_closed(b, a);
    lemma_dts_same_radicand_symmetric(b, dts_add(b, a));
    lemma_dts_same_radicand_transitive(dts_sub(b, a), b, dts_add(b, a));
    lemma_dts_nonneg_radicands_add(b, a);
    lemma_dts_depth_add_le(b, a);
    lemma_dts_nonneg_mul_closed_fuel(dts_sub(b, a), dts_add(b, a), fuel);
    // nonneg(mul(sub(b,a), add(b,a))) ≡ nonneg(sub(b², a²)) by difference_of_squares congruence
    // same_radicand chain for nonneg_fuel_congruence at the end
    lemma_dts_mul_closed(b, b);
    lemma_dts_mul_closed(a, a);
    lemma_dts_mul_closed(dts_sub(b, a), dts_add(b, a));
    lemma_dts_same_radicand_symmetric(b, dts_mul(b, b));
    lemma_dts_same_radicand_symmetric(a, dts_mul(a, a));
    lemma_dts_same_radicand_transitive(dts_mul(b, b), b, a);
    lemma_dts_same_radicand_transitive(dts_mul(b, b), a, dts_mul(a, a));
    lemma_dts_same_radicand_neg(dts_mul(a, a));
    lemma_dts_same_radicand_transitive(dts_mul(b, b), dts_mul(a, a), dts_neg(dts_mul(a, a)));
    lemma_dts_neg_well_formed(dts_mul(a, a));
    lemma_dts_add_closed(dts_mul(b, b), dts_neg(dts_mul(a, a)));
    // difference_of_squares gives eqv(sub(b²,a²), mul(sub(b,a),add(b,a)))
    // I need to transfer nonneg from mul(sub(b,a),add(b,a)) to sub(b²,a²)
    // Use eqv_symmetric + nonneg_fuel_congruence
    lemma_dts_eqv_symmetric(dts_sub(dts_mul(b,b), dts_mul(a,a)),
        dts_mul(dts_sub(b,a), dts_add(b,a)));
    lemma_dts_same_radicand_symmetric(dts_sub(b,a), dts_mul(dts_sub(b,a), dts_add(b,a)));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(b,a), dts_add(b,a)), dts_sub(b,a), b);
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(b,a), dts_add(b,a)), b, dts_mul(b,b));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(b,a), dts_add(b,a)), dts_mul(b,b),
        dts_sub(dts_mul(b,b), dts_mul(a,a)));
    lemma_dts_nonneg_fuel_congruence(
        dts_mul(dts_sub(b,a), dts_add(b,a)),
        dts_sub(dts_mul(b,b), dts_mul(a,a)), fuel);
}

/// le_mul_nonneg_monotone at fuel level: a ≤ b ∧ 0 ≤ c → a*c ≤ b*c.
/// Uses distributivity: (b-a)*c ≡ b*c - a*c. nonneg((b-a)*c) by nonneg_mul IH.
pub proof fn lemma_dts_le_mul_nonneg_monotone_fuel(
    a: DynTowerSpec, b: DynTowerSpec, c: DynTowerSpec, fuel: nat,
)
    requires
        fuel >= dts_depth(a) + 1, fuel >= dts_depth(b) + 1, fuel >= dts_depth(c) + 1,
        dts_well_formed(a), dts_well_formed(b), dts_well_formed(c),
        dts_same_radicand(a, b), dts_same_radicand(b, c),
        dts_nonneg_radicands(a), dts_nonneg_radicands(b), dts_nonneg_radicands(c),
        dts_nonneg_fuel(dts_sub(b, a), fuel),
        dts_nonneg_fuel(c, fuel),
    ensures
        dts_nonneg_fuel(dts_sub(dts_mul(b, c), dts_mul(a, c)), fuel),
    decreases fuel,
{
    // Setup: neg(a) infrastructure + same_radicand chains
    lemma_dts_neg_well_formed(a);
    lemma_dts_same_radicand_neg(a);
    lemma_dts_same_radicand_symmetric(a, dts_neg(a));
    lemma_dts_same_radicand_symmetric(a, b);
    lemma_dts_same_radicand_transitive(b, a, dts_neg(a));
    lemma_dts_same_radicand_transitive(a, b, c);
    lemma_dts_add_closed(b, dts_neg(a));
    lemma_dts_same_radicand_symmetric(b, dts_sub(b, a));
    lemma_dts_same_radicand_transitive(dts_sub(b, a), b, c);
    lemma_dts_nonneg_radicands_neg(a);
    lemma_dts_nonneg_radicands_add(b, dts_neg(a));
    lemma_dts_depth_neg(a);
    lemma_dts_depth_add_le(b, dts_neg(a));
    lemma_dts_nonneg_mul_closed_fuel(dts_sub(b, a), c, fuel);
    // mul(sub(b,a), c) ≡ sub(mul(b,c), mul(a,c)) by neg_mul_left + distributes
    // Actually: mul(b-a, c) = mul(b+neg(a), c). By distributes: mul(b,c) + mul(neg(a),c).
    // mul(neg(a), c) ≡ neg(mul(a,c)) by neg_mul_left.
    // So mul(b-a, c) ≡ mul(b,c) + neg(mul(a,c)) = sub(mul(b,c), mul(a,c)).
    lemma_dts_mul_distributes_left(dts_sub(b, a), b, c);
    // Wait, distributes_left(x, y, z) gives mul(x, add(y,z)). I need mul(sub(b,a), c).
    // That's not in distributes form. Let me use: mul(sub(b,a), c) ≡ mul(c, sub(b,a)) [commutative]
    // Then distributes_left(c, b, neg(a)): mul(c, add(b, neg(a))) ≡ add(mul(c,b), mul(c,neg(a)))
    // mul(c, neg(a)) ≡ neg(mul(c,a)) [neg_mul_right]
    // So mul(sub(b,a), c) ≡ add(mul(c,b), neg(mul(c,a)))
    //                     ≡ add(mul(b,c), neg(mul(a,c))) [commutative × 2]
    //                     = sub(mul(b,c), mul(a,c))
    lemma_dts_same_radicand_symmetric(b, c);
    lemma_dts_same_radicand_transitive(c, b, dts_neg(a));
    lemma_dts_same_radicand_transitive(c, b, a);
    lemma_dts_mul_commutative(dts_sub(b, a), c);
    lemma_dts_mul_distributes_left(c, b, dts_neg(a));
    lemma_dts_neg_mul_right(c, a);
    lemma_dts_mul_commutative(c, b);
    lemma_dts_mul_commutative(c, a);
    lemma_dts_neg_congruence(dts_mul(c, a), dts_mul(a, c));
    lemma_dts_add_congruence_left(dts_mul(c, b), dts_mul(b, c), dts_mul(c, dts_neg(a)));
    lemma_dts_eqv_transitive(dts_mul(c, dts_neg(a)), dts_neg(dts_mul(c, a)), dts_neg(dts_mul(a, c)));
    lemma_dts_add_congruence_right(dts_mul(b, c), dts_mul(c, dts_neg(a)), dts_neg(dts_mul(a, c)));
    // Chain: mul(sub(b,a),c) ≡ mul(c,sub(b,a)) ≡ add(mul(c,b),mul(c,neg(a)))
    //        ≡ add(mul(b,c), neg(mul(a,c))) = sub(mul(b,c), mul(a,c))
    lemma_dts_eqv_transitive(
        dts_mul(dts_sub(b, a), c), dts_mul(c, dts_sub(b, a)),
        dts_add(dts_mul(c, b), dts_mul(c, dts_neg(a))));
    lemma_dts_eqv_transitive(
        dts_add(dts_mul(c, b), dts_mul(c, dts_neg(a))),
        dts_add(dts_mul(b, c), dts_mul(c, dts_neg(a))),
        dts_add(dts_mul(b, c), dts_neg(dts_mul(a, c))));
    lemma_dts_eqv_transitive(
        dts_mul(dts_sub(b, a), c),
        dts_add(dts_mul(c, b), dts_mul(c, dts_neg(a))),
        dts_add(dts_mul(b, c), dts_neg(dts_mul(a, c))));
    // Transfer nonneg via congruence — establish same_radicand for add_closed
    lemma_dts_mul_closed(b, c);
    lemma_dts_mul_closed(a, c);
    lemma_dts_neg_well_formed(dts_mul(a, c));
    lemma_dts_same_radicand_symmetric(a, dts_mul(a, c));
    lemma_dts_same_radicand_symmetric(b, dts_mul(b, c));
    lemma_dts_same_radicand_transitive(dts_mul(b, c), b, a);
    lemma_dts_same_radicand_transitive(dts_mul(b, c), a, dts_mul(a, c));
    lemma_dts_same_radicand_neg(dts_mul(a, c));
    lemma_dts_same_radicand_transitive(dts_mul(b, c), dts_mul(a, c), dts_neg(dts_mul(a, c)));
    lemma_dts_add_closed(dts_mul(b, c), dts_neg(dts_mul(a, c)));
    lemma_dts_mul_closed(dts_sub(b, a), c);
    lemma_dts_same_radicand_symmetric(dts_sub(b, a), dts_mul(dts_sub(b, a), c));
    lemma_dts_same_radicand_transitive(dts_mul(dts_sub(b, a), c), dts_sub(b, a), b);
    lemma_dts_same_radicand_transitive(dts_mul(dts_sub(b, a), c), b, dts_mul(b, c));
    lemma_dts_same_radicand_neg(dts_mul(a, c));
    lemma_dts_same_radicand_symmetric(a, dts_mul(a, c));
    lemma_dts_same_radicand_transitive(dts_mul(b, c), b, a);
    lemma_dts_same_radicand_transitive(dts_mul(b, c), a, dts_mul(a, c));
    lemma_dts_same_radicand_transitive(dts_mul(b, c), dts_mul(a, c), dts_neg(dts_mul(a, c)));
    lemma_dts_same_radicand_symmetric(dts_mul(b, c), dts_add(dts_mul(b, c), dts_neg(dts_mul(a, c))));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(b, a), c), dts_mul(b, c),
        dts_add(dts_mul(b, c), dts_neg(dts_mul(a, c))));
    lemma_dts_nonneg_fuel_congruence(
        dts_mul(dts_sub(b, a), c),
        dts_add(dts_mul(b, c), dts_neg(dts_mul(a, c))), fuel);
}

/// nonneg_radicands preserved by add.
pub proof fn lemma_dts_nonneg_radicands_add(a: DynTowerSpec, b: DynTowerSpec)
    requires
        dts_nonneg_radicands(a), dts_nonneg_radicands(b),
    ensures
        dts_nonneg_radicands(dts_add(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_nonneg_radicands_add(*re1, *re2);
            lemma_dts_nonneg_radicands_add(*im1, *im2);
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_nonneg_radicands_add(DynTowerSpec::Rat(r), *re);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_nonneg_radicands_add(*re, DynTowerSpec::Rat(r));
        }
    }
}

/// nonneg_radicands preserved by neg.
pub proof fn lemma_dts_nonneg_radicands_neg(a: DynTowerSpec)
    requires dts_nonneg_radicands(a),
    ensures dts_nonneg_radicands(dts_neg(a)),
    decreases a,
{
    match a {
        DynTowerSpec::Rat(_) => {}
        DynTowerSpec::Ext(re, im, _) => {
            lemma_dts_nonneg_radicands_neg(*re);
            lemma_dts_nonneg_radicands_neg(*im);
        }
    }
}

/// nonneg_radicands preserved by mul.
pub proof fn lemma_dts_nonneg_radicands_mul(a: DynTowerSpec, b: DynTowerSpec)
    requires
        dts_nonneg_radicands(a), dts_nonneg_radicands(b),
    ensures
        dts_nonneg_radicands(dts_mul(a, b)),
    decreases a, b,
{
    match (a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {}
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            lemma_dts_nonneg_radicands_mul(*re1, *re2);
            lemma_dts_nonneg_radicands_mul(*im1, *im2);
            lemma_dts_nonneg_radicands_mul(*re1, *im2);
            lemma_dts_nonneg_radicands_mul(*im1, *re2);
            lemma_dts_nonneg_radicands_mul(*d, dts_mul(*im1, *im2));
            lemma_dts_nonneg_radicands_add(
                dts_mul(*re1, *re2), dts_mul(*d, dts_mul(*im1, *im2)));
            lemma_dts_nonneg_radicands_add(
                dts_mul(*re1, *im2), dts_mul(*im1, *re2));
        }
        (DynTowerSpec::Rat(r), DynTowerSpec::Ext(re, im, d)) => {
            lemma_dts_nonneg_radicands_mul(DynTowerSpec::Rat(r), *re);
            lemma_dts_nonneg_radicands_mul(DynTowerSpec::Rat(r), *im);
        }
        (DynTowerSpec::Ext(re, im, d), DynTowerSpec::Rat(r)) => {
            lemma_dts_nonneg_radicands_mul(*re, DynTowerSpec::Rat(r));
            lemma_dts_nonneg_radicands_mul(*im, DynTowerSpec::Rat(r));
        }
    }
}

/// Nonneg closed under addition. Mutually recursive with nonneg_mul_closed.
/// Helper for C1+C2 norm bound: establishes nonneg(sub(sum_re², d*sum_im²))
/// at fuel f. Part of the mutual recursion group.
#[verifier::rlimit(120)]
pub proof fn lemma_dts_c1c2_norm_bound(
    a1: DynTowerSpec, b1: DynTowerSpec, a2: DynTowerSpec, b2: DynTowerSpec,
    dd: DynTowerSpec, f: nat,
)
    requires
        f >= dts_depth(a1) + 1, f >= dts_depth(b1) + 1,
        f >= dts_depth(a2) + 1, f >= dts_depth(b2) + 1,
        f >= dts_depth(dd) + 1,
        dts_well_formed(a1), dts_well_formed(b1), dts_well_formed(a2), dts_well_formed(b2),
        dts_well_formed(dd),
        dts_same_radicand(a1, b1), dts_same_radicand(a1, a2),
        dts_same_radicand(a1, b2), dts_same_radicand(a1, dd),
        dts_nonneg_radicands(a1), dts_nonneg_radicands(b1),
        dts_nonneg_radicands(a2), dts_nonneg_radicands(b2),
        dts_nonneg_radicands(dd), dts_nonneg(dd),
        dts_nonneg_fuel(a1, f), dts_nonneg_fuel(a2, f),
        // One of b1,b2 nonneg, other not. Both a's nonneg.
        (dts_nonneg_fuel(b1, f) && !dts_nonneg_fuel(b2, f))
            || (!dts_nonneg_fuel(b1, f) && dts_nonneg_fuel(b2, f)),
        // sum_im < 0
        !dts_nonneg_fuel(dts_add(b1, b2), f),
        !dts_is_zero(dts_add(b1, b2)),
        // C2 norm bound from the C2 side
        dts_nonneg_fuel(b1, f) ==>
            dts_nonneg_fuel(dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2))), f),
        dts_nonneg_fuel(b2, f) ==>
            dts_nonneg_fuel(dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1))), f),
    ensures
        dts_nonneg_fuel(
            dts_sub(
                dts_mul(dts_add(a1, a2), dts_add(a1, a2)),
                dts_mul(dd, dts_mul(dts_add(b1, b2), dts_add(b1, b2)))),
            f),
    decreases f, 1nat,
{
    // Chain: (a1+a2)² ≥ r² ≥ d*s² ≥ d*(b1+b2)²
    // where r is the C2 side's re, s is the C2 side's im.
    let b1_nn = dts_nonneg_fuel(b1, f);
    let r = if b1_nn { a2 } else { a1 };
    let p = if b1_nn { a1 } else { a2 };
    let s = if b1_nn { b2 } else { b1 };
    let sum_re = dts_add(a1, a2);
    let sum_im = dts_add(b1, b2);
    let r_sq = dts_mul(r, r);
    let s_sq = dts_mul(s, s);
    let sum_re_sq = dts_mul(sum_re, sum_re);
    let d_s_sq = dts_mul(dd, s_sq);

    // ═══ Infrastructure ═══
    // Derive same_radicand(b1, b2) from a1~b1 and a1~b2
    lemma_dts_same_radicand_symmetric(a1, b1);
    lemma_dts_same_radicand_transitive(b1, a1, b2);
    lemma_dts_add_closed(a1, a2);
    lemma_dts_add_closed(b1, b2);
    lemma_dts_same_radicand_symmetric(a1, a2);
    lemma_dts_same_radicand_symmetric(b1, b2);
    lemma_dts_same_radicand_transitive(b2, b1, dts_add(b1, b2));
    lemma_dts_same_radicand_symmetric(a1, dts_add(a1, a2));
    lemma_dts_same_radicand_transitive(sum_re, a1, a2);
    lemma_dts_depth_add_le(a1, a2);
    lemma_dts_depth_add_le(b1, b2);
    lemma_dts_nonneg_radicands_add(a1, a2);
    lemma_dts_nonneg_radicands_add(b1, b2);
    // same_radicand for ghost p,r,s
    lemma_dts_same_radicand_symmetric(a1, a2);
    // sr(s, sum_im): s ∈ {b1,b2}, sum_im = add(b1,b2)
    lemma_dts_same_radicand_symmetric(b1, b2);
    lemma_dts_same_radicand_transitive(b2, b1, dts_add(b1, b2));

    // ═══ T1: (a1+a2)² ≥ r² via difference_of_squares ═══
    // sub(sum_re, r) ≡ p by add_then_sub_cancel
    if b1_nn {
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(a1, a2);
    } else {
        DynTowerSpec::axiom_add_commutative(a1, a2);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(a2, a1);
        lemma_dts_add_congruence_left(
            dts_add(a1, a2), dts_add(a2, a1), dts_neg(a1));
    }
    // nonneg(sub(sum_re, r)) from nonneg(p) by congruence
    lemma_dts_neg_well_formed(r);
    lemma_dts_same_radicand_neg(r);
    lemma_dts_same_radicand_symmetric(r, dts_neg(r));
    lemma_dts_same_radicand_transitive(sum_re, r, dts_neg(r));
    lemma_dts_add_closed(sum_re, dts_neg(r));
    lemma_dts_depth_neg(r);
    lemma_dts_depth_add_le(sum_re, dts_neg(r));
    lemma_dts_same_radicand_symmetric(sum_re, dts_sub(sum_re, r));
    // same_radicand(r, sum_re): r ∈ {a1,a2}, both same_radicand with a1
    // a1 ~ add(a1,a2) from add_closed. a2 ~ a1 (symmetric) ~ add(a1,a2).
    lemma_dts_same_radicand_transitive(a2, a1, sum_re);
    // Now Z3 has sr(a1, sum_re) and sr(a2, sum_re). So sr(r, sum_re) ✓.
    assert(dts_same_radicand(r, sum_re));
    assert(dts_same_radicand(p, r));
    lemma_dts_same_radicand_transitive(p, r, sum_re);
    lemma_dts_same_radicand_symmetric(r, sum_re);
    lemma_dts_same_radicand_transitive(p, sum_re, dts_sub(sum_re, r));
    lemma_dts_same_radicand_symmetric(p, dts_sub(sum_re, r));
    lemma_dts_nonneg_radicands_neg(r);
    lemma_dts_nonneg_radicands_add(sum_re, dts_neg(r));
    // nonneg(sub(sum_re, r)): transfer from nonneg(p)
    // Split by branch to help Z3 with ghost variables
    if b1_nn {
        // sub(add(a1,a2), a2) ≡ a1 → symmetric → a1 ≡ sub(sum_re, a2)
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(a1, a2);
        lemma_dts_eqv_symmetric(dts_sub(dts_add(a1, a2), a2), a1);
        lemma_dts_nonneg_fuel_congruence(a1, dts_sub(sum_re, a2), f);
    } else {
        // sub(add(a1,a2), a1): commutative + cancel
        DynTowerSpec::axiom_add_commutative(a1, a2);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(a2, a1);
        lemma_dts_add_congruence_left(
            dts_add(a1, a2), dts_add(a2, a1), dts_neg(a1));
        // sub(add(a2,a1), a1) ≡ a2 [add_then_sub]. symmetric: a2 ≡ sub(add(a2,a1), a1).
        lemma_dts_eqv_symmetric(dts_sub(dts_add(a2, a1), a1), a2);
        // sub(add(a1,a2), a1) ≡ sub(add(a2,a1), a1) [add_congruence from commutative].
        // symmetric: sub(add(a2,a1), a1) ≡ sub(add(a1,a2), a1).
        lemma_dts_eqv_symmetric(
            dts_sub(dts_add(a1, a2), a1), dts_sub(dts_add(a2, a1), a1));
        // chain: a2 ≡ sub(add(a2,a1), a1) ≡ sub(add(a1,a2), a1)
        lemma_dts_eqv_transitive(
            a2, dts_sub(dts_add(a2, a1), a1), dts_sub(dts_add(a1, a2), a1));
        lemma_dts_nonneg_fuel_congruence(a2, dts_sub(sum_re, a1), f);
    }
    // difference_of_squares(r, sum_re)
    lemma_dts_same_radicand_symmetric(r, sum_re);
    lemma_dts_same_radicand_reflexive(r);
    lemma_dts_same_radicand_reflexive(sum_re);
    lemma_dts_difference_of_squares(r, sum_re);
    // nonneg(add(sum_re, r)) by nonneg_add IH — split by branch
    lemma_dts_nonneg_radicands_add(a1, a2);
    // nonneg(sum_re) from nonneg(a1) + nonneg(a2) by IH
    lemma_dts_nonneg_add_closed_fuel(a1, a2, f);
    // nonneg(add(sum_re, r)) by nonneg_add IH (sum_re nonneg, r nonneg)
    if b1_nn {
        lemma_dts_same_radicand_symmetric(a2, sum_re);
        lemma_dts_nonneg_add_closed_fuel(sum_re, a2, f);
    } else {
        lemma_dts_same_radicand_symmetric(a1, sum_re);
        lemma_dts_nonneg_add_closed_fuel(sum_re, a1, f);
    }
    // nonneg(mul(sub(sum_re,r), add(sum_re,r))) by nonneg_mul IH
    lemma_dts_add_closed(sum_re, r);
    lemma_dts_same_radicand_symmetric(sum_re, dts_add(sum_re, r));
    lemma_dts_same_radicand_transitive(
        dts_sub(sum_re, r), sum_re, dts_add(sum_re, r));
    lemma_dts_nonneg_radicands_add(sum_re, r);
    lemma_dts_depth_add_le(sum_re, r);
    lemma_dts_nonneg_mul_closed_fuel(
        dts_sub(sum_re, r), dts_add(sum_re, r), f);
    // Transfer: mul(sub,add) → sub(sum_re², r²)
    lemma_dts_mul_closed(sum_re, sum_re);
    lemma_dts_mul_closed(r, r);
    lemma_dts_mul_closed(dts_sub(sum_re, r), dts_add(sum_re, r));
    lemma_dts_same_radicand_symmetric(sum_re, sum_re_sq);
    lemma_dts_same_radicand_transitive(sum_re_sq, sum_re, r);
    lemma_dts_same_radicand_symmetric(r, r_sq);
    lemma_dts_same_radicand_transitive(sum_re_sq, r, r_sq);
    lemma_dts_same_radicand_neg(r_sq);
    lemma_dts_same_radicand_transitive(sum_re_sq, r_sq, dts_neg(r_sq));
    lemma_dts_neg_well_formed(r_sq);
    lemma_dts_add_closed(sum_re_sq, dts_neg(r_sq));
    lemma_dts_same_radicand_symmetric(
        dts_sub(sum_re, r), dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
        dts_sub(sum_re, r), sum_re);
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
        sum_re, sum_re_sq);
    lemma_dts_same_radicand_symmetric(
        sum_re_sq, dts_sub(sum_re_sq, r_sq));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
        sum_re_sq, dts_sub(sum_re_sq, r_sq));
    lemma_dts_eqv_symmetric(dts_sub(sum_re_sq, r_sq),
        dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)));
    lemma_dts_nonneg_fuel_congruence(
        dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
        dts_sub(sum_re_sq, r_sq), f);
    // T1 done: nonneg(sub(sum_re², r²)) ✓

    // ═══ T1+T2 chain ═══
    lemma_dts_same_radicand_reflexive(s);
    lemma_dts_mul_closed(s, s);
    lemma_dts_same_radicand_symmetric(a1, dd);
    lemma_dts_same_radicand_transitive(dd, a1, b1);
    lemma_dts_same_radicand_transitive(dd, b1, s);
    lemma_dts_same_radicand_symmetric(s, s_sq);
    lemma_dts_same_radicand_transitive(dd, s, s_sq);
    lemma_dts_mul_closed(dd, s_sq);
    lemma_dts_nonneg_radicands_mul(s, s);
    lemma_dts_nonneg_radicands_mul(dd, s_sq);
    // same_radicand(r_sq, r) and same_radicand(r, dd) for ghost r
    lemma_dts_same_radicand_reflexive(r);
    lemma_dts_mul_closed(r, r);
    lemma_dts_same_radicand_symmetric(r, r_sq);
    // same_radicand(r, dd): r ∈ {a2, a1}. a1~dd is precond. For a2: need transitive(a2, a1, dd).
    if b1_nn {
        lemma_dts_same_radicand_symmetric(a1, a2);
        lemma_dts_same_radicand_transitive(a2, a1, dd);
    }
    // same_radicand chains for sub terms
    lemma_dts_same_radicand_transitive(r_sq, r, dd);
    lemma_dts_same_radicand_symmetric(dd, d_s_sq);
    lemma_dts_same_radicand_transitive(r_sq, dd, d_s_sq);
    lemma_dts_same_radicand_neg(d_s_sq);
    lemma_dts_same_radicand_transitive(r_sq, d_s_sq, dts_neg(d_s_sq));
    lemma_dts_neg_well_formed(d_s_sq);
    lemma_dts_add_closed(r_sq, dts_neg(d_s_sq));
    lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, r_sq));
    lemma_dts_same_radicand_symmetric(r_sq, dts_sub(r_sq, d_s_sq));
    lemma_dts_same_radicand_transitive(
        dts_sub(sum_re_sq, r_sq), sum_re_sq, r_sq);
    lemma_dts_same_radicand_transitive(
        dts_sub(sum_re_sq, r_sq), r_sq, dts_sub(r_sq, d_s_sq));
    lemma_dts_nonneg_radicands_mul(sum_re, sum_re);
    lemma_dts_nonneg_radicands_mul(r, r);
    lemma_dts_nonneg_radicands_neg(r_sq);
    lemma_dts_nonneg_radicands_add(sum_re_sq, dts_neg(r_sq));
    lemma_dts_nonneg_radicands_neg(d_s_sq);
    lemma_dts_nonneg_radicands_add(r_sq, dts_neg(d_s_sq));
    lemma_dts_depth_mul_le(sum_re, sum_re);
    lemma_dts_depth_mul_le(r, r);
    lemma_dts_depth_mul_le(s, s);
    lemma_dts_depth_mul_le(dd, s_sq);
    lemma_dts_depth_neg(r_sq);
    lemma_dts_depth_add_le(sum_re_sq, dts_neg(r_sq));
    lemma_dts_depth_neg(d_s_sq);
    lemma_dts_depth_add_le(r_sq, dts_neg(d_s_sq));
    // T2: nonneg(sub(r², d*s²)) from C2 norm bound
    assert(dts_nonneg_fuel(dts_sub(r_sq, d_s_sq), f));
    assert(dts_depth(r) <= dts_depth(a1) || dts_depth(r) <= dts_depth(a2));
    assert(dts_depth(s) <= dts_depth(b1) || dts_depth(s) <= dts_depth(b2));
    lemma_dts_nonneg_add_closed_fuel(
        dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq), f);
    // sub_add_sub chain
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_add_sub::<DynTowerSpec>(
        sum_re_sq, r_sq, d_s_sq);
    lemma_dts_add_closed(
        dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq));
    lemma_dts_same_radicand_symmetric(
        dts_sub(sum_re_sq, r_sq),
        dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)));
    lemma_dts_same_radicand_transitive(sum_re_sq, r_sq, d_s_sq);
    lemma_dts_same_radicand_transitive(sum_re_sq, d_s_sq, dts_neg(d_s_sq));
    lemma_dts_add_closed(sum_re_sq, dts_neg(d_s_sq));
    lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, d_s_sq));
    lemma_dts_same_radicand_transitive(
        dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
        dts_sub(sum_re_sq, r_sq), sum_re_sq);
    lemma_dts_same_radicand_transitive(
        dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
        sum_re_sq, dts_sub(sum_re_sq, d_s_sq));
    lemma_dts_nonneg_fuel_congruence(
        dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
        dts_sub(sum_re_sq, d_s_sq), f);
    // nonneg(sub(sum_re², d*s²)) ✓

    // ═══ T3: s² ≥ sum_im² via neg square_le_square ═══
    let ns = dts_neg(s);
    let nsm = dts_neg(sum_im);
    lemma_dts_neg_well_formed(s);
    lemma_dts_neg_well_formed(sum_im);
    lemma_dts_same_radicand_neg(s);
    lemma_dts_same_radicand_neg(sum_im);
    lemma_dts_same_radicand_symmetric(s, ns);
    lemma_dts_same_radicand_symmetric(sum_im, nsm);
    lemma_dts_same_radicand_transitive(ns, s, sum_im);
    lemma_dts_same_radicand_transitive(ns, sum_im, nsm);
    lemma_dts_nonneg_radicands_neg(s);
    lemma_dts_nonneg_radicands_neg(sum_im);
    lemma_dts_depth_neg(s);
    lemma_dts_depth_neg(sum_im);
    // nonneg(sub(ns, nsm)) from nonneg(q) via congruence
    let q = if b1_nn { b1 } else { b2 };
    lemma_dts_same_radicand_symmetric(ns, nsm);
    lemma_dts_same_radicand_symmetric(nsm, ns);
    lemma_dts_neg_well_formed(nsm);
    lemma_dts_same_radicand_neg(nsm);
    lemma_dts_same_radicand_transitive(ns, nsm, dts_neg(nsm));
    lemma_dts_add_closed(ns, dts_neg(nsm));
    lemma_dts_nonneg_radicands_neg(nsm);
    lemma_dts_nonneg_radicands_add(ns, dts_neg(nsm));
    lemma_dts_depth_neg(nsm);
    lemma_dts_depth_add_le(ns, dts_neg(nsm));
    lemma_dts_neg_involution(sum_im);
    if b1_nn {
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(b1, b2);
    } else {
        DynTowerSpec::axiom_add_commutative(b1, b2);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
            DynTowerSpec>(b2, b1);
        lemma_dts_add_congruence_left(
            dts_add(b1, b2), dts_add(b2, b1), dts_neg(b1));
        // Chain: sub(sum_im, b1) ≡ sub(add(b2,b1), b1) ≡ b2 = sub(sum_im, s) ≡ q
        lemma_dts_eqv_transitive(
            dts_sub(dts_add(b1, b2), b1),
            dts_sub(dts_add(b2, b1), b1),
            b2);
    }
    // sub(sum_im, s) ≡ q. Chain to sub(ns, nsm) via neg_involution + add_congruence.
    lemma_dts_add_congruence_right(dts_neg(s), dts_neg(nsm), sum_im);
    DynTowerSpec::axiom_add_commutative(dts_neg(s), sum_im);
    lemma_dts_eqv_transitive(
        dts_sub(ns, nsm), dts_add(dts_neg(s), sum_im), dts_sub(sum_im, s));
    // eqv(sub(sum_im, s), q) from if/else block above
    lemma_dts_eqv_transitive(dts_sub(ns, nsm), dts_sub(sum_im, s), q);
    lemma_dts_eqv_symmetric(dts_sub(ns, nsm), q);
    // same_radicand(q, ns) for ghost variables: q ∈ {b1,b2}, ns = neg(s), s ∈ {b2,b1}
    if b1_nn {
        // q=b1, ns=neg(b2). b1~b2 (line 3372), b2~neg(b2) (same_radicand_neg).
        lemma_dts_same_radicand_transitive(b1, b2, dts_neg(b2));
    } else {
        // q=b2, ns=neg(b1). b2~b1 (symmetric), b1~neg(b1) (same_radicand_neg).
        lemma_dts_same_radicand_symmetric(b1, b2);
        lemma_dts_same_radicand_transitive(b2, b1, dts_neg(b1));
    }
    lemma_dts_same_radicand_transitive(q, ns, dts_sub(ns, nsm));
    lemma_dts_same_radicand_symmetric(q, dts_sub(ns, nsm));
    lemma_dts_nonneg_fuel_congruence(q, dts_sub(ns, nsm), f);
    // Inline square_le_square(nsm, ns)
    // Establish nonneg(ns, f) and nonneg(nsm, f) via le_total
    // !nonneg(s, f) since s is the non-nonneg b. !nonneg(sum_im, f) from precondition.
    lemma_dts_nonneg_or_neg_nonneg_fuel(s, f);
    lemma_dts_nonneg_or_neg_nonneg_fuel(sum_im, f);
    lemma_dts_same_radicand_symmetric(nsm, ns);
    lemma_dts_difference_of_squares(nsm, ns);
    lemma_dts_nonneg_add_closed_fuel(ns, nsm, f);
    lemma_dts_add_closed(ns, nsm);
    lemma_dts_same_radicand_symmetric(ns, dts_add(ns, nsm));
    // same_radicand(sub(ns, nsm), ns) from add_closed(ns, neg(nsm)) + symmetric
    lemma_dts_same_radicand_symmetric(ns, dts_sub(ns, nsm));
    lemma_dts_same_radicand_transitive(dts_sub(ns, nsm), ns, dts_add(ns, nsm));
    lemma_dts_nonneg_radicands_add(ns, nsm);
    lemma_dts_depth_add_le(ns, nsm);
    lemma_dts_nonneg_mul_closed_fuel(dts_sub(ns, nsm), dts_add(ns, nsm), f);
    // Transfer: mul(...) → sub(ns², nsm²)
    let ns_sq = dts_mul(ns, ns);
    let nsm_sq = dts_mul(nsm, nsm);
    let sum_im_sq = dts_mul(sum_im, sum_im);
    lemma_dts_same_radicand_reflexive(ns);
    lemma_dts_same_radicand_reflexive(nsm);
    lemma_dts_mul_closed(ns, ns);
    lemma_dts_mul_closed(nsm, nsm);
    lemma_dts_mul_closed(dts_sub(ns, nsm), dts_add(ns, nsm));
    lemma_dts_same_radicand_symmetric(ns, ns_sq);
    lemma_dts_same_radicand_transitive(ns_sq, ns, nsm);
    lemma_dts_same_radicand_symmetric(nsm, nsm_sq);
    lemma_dts_same_radicand_transitive(ns_sq, nsm, nsm_sq);
    lemma_dts_same_radicand_neg(nsm_sq);
    lemma_dts_same_radicand_transitive(ns_sq, nsm_sq, dts_neg(nsm_sq));
    lemma_dts_neg_well_formed(nsm_sq);
    lemma_dts_add_closed(ns_sq, dts_neg(nsm_sq));
    lemma_dts_same_radicand_symmetric(
        dts_sub(ns, nsm), dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)), dts_sub(ns, nsm), ns);
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)), ns, ns_sq);
    lemma_dts_same_radicand_symmetric(ns_sq, dts_sub(ns_sq, nsm_sq));
    lemma_dts_same_radicand_transitive(
        dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)), ns_sq, dts_sub(ns_sq, nsm_sq));
    lemma_dts_eqv_symmetric(dts_sub(ns_sq, nsm_sq),
        dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)));
    lemma_dts_nonneg_fuel_congruence(
        dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)), dts_sub(ns_sq, nsm_sq), f);
    // Transfer: sub(neg(s)², neg(sum_im)²) → sub(s², sum_im²) via neg_mul_neg
    lemma_dts_same_radicand_reflexive(sum_im);
    lemma_dts_neg_mul_neg(s, s);
    lemma_dts_neg_mul_neg(sum_im, sum_im);
    lemma_dts_mul_closed(s, s);
    lemma_dts_mul_closed(sum_im, sum_im);
    lemma_dts_same_radicand_symmetric(ns, ns_sq);
    lemma_dts_same_radicand_transitive(ns_sq, ns, s);
    lemma_dts_same_radicand_symmetric(s, s_sq);
    lemma_dts_same_radicand_transitive(ns_sq, s, s_sq);
    lemma_dts_same_radicand_symmetric(nsm, nsm_sq);
    lemma_dts_same_radicand_transitive(nsm_sq, nsm, sum_im);
    lemma_dts_same_radicand_symmetric(sum_im, sum_im_sq);
    lemma_dts_same_radicand_transitive(nsm_sq, sum_im, sum_im_sq);
    lemma_dts_sub_congruence_both(ns_sq, nsm_sq, s_sq, sum_im_sq);
    lemma_dts_nonneg_fuel_congruence(
        dts_sub(ns_sq, nsm_sq), dts_sub(s_sq, sum_im_sq), f);
    // nonneg(sub(s², sum_im²)) ✓

    // ═══ d * (s² - sum_im²) ≥ 0 ═══
    lemma_dts_nonneg_radicands_mul(s, s);
    lemma_dts_nonneg_radicands_mul(sum_im, sum_im);
    lemma_dts_nonneg_radicands_neg(sum_im_sq);
    lemma_dts_nonneg_radicands_add(s_sq, dts_neg(sum_im_sq));
    lemma_dts_same_radicand_transitive(s_sq, s, sum_im);
    lemma_dts_same_radicand_transitive(s_sq, sum_im, sum_im_sq);
    lemma_dts_same_radicand_neg(sum_im_sq);
    lemma_dts_same_radicand_transitive(s_sq, sum_im_sq, dts_neg(sum_im_sq));
    lemma_dts_neg_well_formed(sum_im_sq);
    lemma_dts_add_closed(s_sq, dts_neg(sum_im_sq));
    lemma_dts_same_radicand_symmetric(s_sq, dts_sub(s_sq, sum_im_sq));
    lemma_dts_same_radicand_transitive(dd, s_sq, dts_sub(s_sq, sum_im_sq));
    lemma_dts_depth_mul_le(sum_im, sum_im);
    lemma_dts_depth_neg(sum_im_sq);
    lemma_dts_depth_add_le(s_sq, dts_neg(sum_im_sq));
    lemma_dts_nonneg_fuel_stabilize(dd, f);
    lemma_dts_nonneg_mul_closed_fuel(dd, dts_sub(s_sq, sum_im_sq), f);
    // mul(d, sub(s², sum_im²)) ≡ sub(d*s², d*sum_im²) via distributes + neg_mul_right
    let d_sum_im_sq = dts_mul(dd, sum_im_sq);
    lemma_dts_same_radicand_transitive(dd, s, sum_im);
    lemma_dts_same_radicand_transitive(dd, sum_im, sum_im_sq);
    lemma_dts_mul_distributes_left(dd, s_sq, dts_neg(sum_im_sq));
    lemma_dts_neg_mul_right(dd, sum_im_sq);
    lemma_dts_add_congruence_right(
        dts_mul(dd, s_sq), dts_mul(dd, dts_neg(sum_im_sq)), dts_neg(d_sum_im_sq));
    lemma_dts_eqv_transitive(
        dts_mul(dd, dts_sub(s_sq, sum_im_sq)),
        dts_add(dts_mul(dd, s_sq), dts_mul(dd, dts_neg(sum_im_sq))),
        dts_add(d_s_sq, dts_neg(d_sum_im_sq)));
    // Transfer nonneg
    lemma_dts_mul_closed(dd, sum_im_sq);
    lemma_dts_neg_well_formed(d_sum_im_sq);
    lemma_dts_same_radicand_symmetric(dd, d_s_sq);
    lemma_dts_same_radicand_symmetric(dd, d_sum_im_sq);
    lemma_dts_same_radicand_transitive(d_s_sq, dd, d_sum_im_sq);
    lemma_dts_same_radicand_neg(d_sum_im_sq);
    lemma_dts_same_radicand_transitive(d_s_sq, d_sum_im_sq, dts_neg(d_sum_im_sq));
    lemma_dts_add_closed(d_s_sq, dts_neg(d_sum_im_sq));
    lemma_dts_mul_closed(dd, dts_sub(s_sq, sum_im_sq));
    lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_sub(s_sq, sum_im_sq)));
    lemma_dts_same_radicand_transitive(
        dts_mul(dd, dts_sub(s_sq, sum_im_sq)), dd, d_s_sq);
    lemma_dts_same_radicand_symmetric(d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
    lemma_dts_same_radicand_transitive(
        dts_mul(dd, dts_sub(s_sq, sum_im_sq)), d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
    lemma_dts_nonneg_fuel_congruence(
        dts_mul(dd, dts_sub(s_sq, sum_im_sq)), dts_sub(d_s_sq, d_sum_im_sq), f);
    // nonneg(sub(d*s², d*sum_im²)) ✓ = T3

    // ═══ Final chain: T1+T2+T3 ═══
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_add_sub::<DynTowerSpec>(
        sum_re_sq, d_s_sq, d_sum_im_sq);
    lemma_dts_same_radicand_symmetric(d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
    lemma_dts_same_radicand_transitive(
        dts_sub(sum_re_sq, d_s_sq), sum_re_sq, d_s_sq);
    lemma_dts_same_radicand_transitive(
        dts_sub(sum_re_sq, d_s_sq), d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
    lemma_dts_nonneg_radicands_mul(dd, sum_im_sq);
    lemma_dts_nonneg_radicands_neg(d_sum_im_sq);
    lemma_dts_nonneg_radicands_add(d_s_sq, dts_neg(d_sum_im_sq));
    lemma_dts_nonneg_radicands_add(sum_re_sq, dts_neg(d_s_sq));
    lemma_dts_depth_neg(d_sum_im_sq);
    lemma_dts_depth_add_le(d_s_sq, dts_neg(d_sum_im_sq));
    // depth bounds for d_sum_im_sq and sub(sum_re_sq, d_s_sq)
    lemma_dts_depth_mul_le(dd, sum_im_sq);
    lemma_dts_depth_add_le(sum_re_sq, dts_neg(d_s_sq));
    lemma_dts_nonneg_add_closed_fuel(
        dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq), f);
    // Transfer via sub_add_sub congruence
    lemma_dts_add_closed(
        dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq));
    lemma_dts_same_radicand_transitive(sum_re_sq, d_s_sq, d_sum_im_sq);
    lemma_dts_same_radicand_neg(d_sum_im_sq);
    lemma_dts_same_radicand_transitive(sum_re_sq, d_sum_im_sq, dts_neg(d_sum_im_sq));
    lemma_dts_add_closed(sum_re_sq, dts_neg(d_sum_im_sq));
    lemma_dts_same_radicand_symmetric(
        dts_sub(sum_re_sq, d_s_sq),
        dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)));
    lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, d_sum_im_sq));
    lemma_dts_same_radicand_transitive(
        dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
        dts_sub(sum_re_sq, d_s_sq), sum_re_sq);
    lemma_dts_same_radicand_transitive(
        dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
        sum_re_sq, dts_sub(sum_re_sq, d_sum_im_sq));
    lemma_dts_nonneg_fuel_congruence(
        dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
        dts_sub(sum_re_sq, d_sum_im_sq), f);
    // nonneg(sub(sum_re², d*sum_im²)) ✓
}

#[verifier::rlimit(80)]
pub proof fn lemma_dts_nonneg_add_closed_fuel(
    x: DynTowerSpec, y: DynTowerSpec, fuel: nat,
)
    requires
        fuel >= dts_depth(x) + 1, fuel >= dts_depth(y) + 1,
        dts_well_formed(x), dts_well_formed(y),
        dts_same_radicand(x, y),
        dts_nonneg_radicands(x), dts_nonneg_radicands(y),
        dts_nonneg_fuel(x, fuel), dts_nonneg_fuel(y, fuel),
    ensures
        dts_nonneg_fuel(dts_add(x, y), fuel),
    decreases fuel, 0nat,
{
    match (x, y) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            verus_algebra::inequalities::lemma_nonneg_add::<Rational>(r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            let f = (fuel - 1) as nat;
            let a1 = *re1; let b1 = *im1; let dd = *d;
            let a2 = *re2; let b2 = *im2;
            lemma_dts_depth_add_le(a1, a2);
            lemma_dts_depth_add_le(b1, b2);
            let a1_nn = dts_nonneg_fuel(a1, f);
            let b1_nn = dts_nonneg_fuel(b1, f);
            let a2_nn = dts_nonneg_fuel(a2, f);
            let b2_nn = dts_nonneg_fuel(b2, f);
            // C1+C1: both re,im nonneg → sum has C1
            if a1_nn && b1_nn && a2_nn && b2_nn {
                lemma_dts_nonneg_add_closed_fuel(a1, a2, f);
                lemma_dts_nonneg_add_closed_fuel(b1, b2, f);
                return;
            }
            // C1+C2 or C2+C1: one has im≥0, other has im<0, both re≥0
            if a1_nn && a2_nn && ((b1_nn && !b2_nn) || (!b1_nn && b2_nn)) {
                // sum_re = a1+a2: nonneg by IH (both re nonneg)
                lemma_dts_nonneg_add_closed_fuel(a1, a2, f);
                // Check sign of sum_im = b1+b2
                lemma_dts_add_closed(b1, b2);
                lemma_dts_nonneg_or_neg_nonneg_fuel(dts_add(b1, b2), f);
                if dts_nonneg_fuel(dts_add(b1, b2), f) {
                    return; // C1: re≥0, im≥0
                }
                // sum_im < 0. Need C2: re≥0, neg(im) nonneg, !is_zero(im), norm≥0
                if dts_is_zero(dts_add(b1, b2)) {
                    lemma_dts_is_zero_implies_eqv_zero(dts_add(b1, b2));
                    lemma_dts_nonneg_fuel_zero(dts_add(b1, b2), f);
                }
                // norm≥0: (a1+a2)² - d*(b1+b2)² ≥ 0 via extracted helper
                lemma_dts_same_radicand_symmetric(a1, dd);
                lemma_dts_same_radicand_transitive(a1, b1, b2);
                lemma_dts_c1c2_norm_bound(a1, b1, a2, b2, dd, f);
                return;
            }
            // TODO: C1+C3, C3+C1, C2+C2, C2+C3, C3+C2, C3+C3
            if false { // placeholder to keep function compiling
                let sum_re = dts_add(a1, a2);
                let sum_im = dts_add(b1, b2);
                // ── T1: (a1+a2)² ≥ r² ──
                // sub(sum_re, r) ≡ p by add_then_sub_cancel. nonneg(p) ✓.
                // difference_of_squares(r, sum_re): sub(sum_re², r²) ≡ mul(sub(sum_re,r), add(sum_re,r))
                // nonneg(sub(sum_re,r)) ✓ (from p nonneg + congruence)
                // nonneg(add(sum_re,r)): sum_re ≥ 0 [already proved], r ≥ 0 → nonneg_add IH
                // nonneg_mul IH → nonneg(mul(sub(sum_re,r), add(sum_re,r)))
                // congruence → nonneg(sub(sum_re², r²))
                let r = if b1_nn { a2 } else { a1 };
                let p = if b1_nn { a1 } else { a2 };
                let s = if b1_nn { b2 } else { b1 };
                let r_sq = dts_mul(r, r);
                let s_sq = dts_mul(s, s);
                let sum_re_sq = dts_mul(sum_re, sum_re);
                let sum_im_sq = dts_mul(sum_im, sum_im);

                // Infrastructure
                lemma_dts_add_closed(a1, a2);
                lemma_dts_same_radicand_reflexive(r);
                lemma_dts_same_radicand_reflexive(s);
                lemma_dts_same_radicand_reflexive(sum_re);
                lemma_dts_same_radicand_reflexive(sum_im);
                lemma_dts_same_radicand_symmetric(a1, a2);
                lemma_dts_same_radicand_symmetric(a1, sum_re);
                lemma_dts_same_radicand_transitive(sum_re, a1, a2);

                // sub(sum_re, r) ≡ p via add_then_sub_cancel
                verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                    DynTowerSpec>(p, r);
                // (p+r) - r ≡ p. And sum_re = add(a1,a2).
                // If b1_nn: sum_re = add(a1,a2) = add(p,r). OK.
                // If !b1_nn: sum_re = add(a1,a2) = add(r,p). Need commutative.
                if !b1_nn {
                    DynTowerSpec::axiom_add_commutative(a1, a2);
                }
                // nonneg(sub(sum_re, r)) from nonneg(p) by congruence
                // sub(sum_re, r) ≡ sub(add(p,r), r) ≡ p
                lemma_dts_neg_well_formed(r);
                lemma_dts_same_radicand_neg(r);
                lemma_dts_same_radicand_symmetric(r, dts_neg(r));
                lemma_dts_same_radicand_transitive(sum_re, r, dts_neg(r));
                lemma_dts_add_closed(sum_re, dts_neg(r));
                lemma_dts_depth_neg(r);
                lemma_dts_depth_add_le(sum_re, dts_neg(r));
                lemma_dts_same_radicand_symmetric(sum_re, dts_sub(sum_re, r));
                // same_radicand(p, r) and (r, sum_re): establish for both branches
                lemma_dts_same_radicand_symmetric(a1, a2);
                // Now Z3 has both sr(a1,a2) and sr(a2,a1).
                // sr(r, sum_re): add_closed gives sr(a1, add(a1,a2)).
                // If r=a2: sr(a2, a1) + sr(a1, add(a1,a2)) → sr(a2, add(a1,a2))
                // If r=a1: sr(a1, add(a1,a2)) directly ✓
                lemma_dts_same_radicand_transitive(a2, a1, sum_re);
                // Now sr(a2, sum_re) ✓. And sr(a1, sum_re) from add_closed.
                assert(dts_same_radicand(p, r));
                assert(dts_same_radicand(r, sum_re));
                lemma_dts_same_radicand_transitive(p, sum_re, dts_sub(sum_re, r));
                lemma_dts_same_radicand_symmetric(p, dts_sub(sum_re, r));
                lemma_dts_nonneg_radicands_neg(r);
                lemma_dts_nonneg_radicands_add(a1, a2);
                lemma_dts_nonneg_radicands_add(sum_re, dts_neg(r));
                // Establish eqv(p, sub(sum_re, r)) explicitly for both branches
                if b1_nn {
                    // p=a1, r=a2. sub(add(a1,a2), a2) ≡ a1 by add_then_sub_cancel
                    lemma_dts_eqv_symmetric(dts_sub(dts_add(a1, a2), a2), a1);
                } else {
                    // p=a2, r=a1. sub(add(a1,a2), a1).
                    // add(a1,a2) ≡ add(a2,a1) by commutative (already called)
                    // sub(add(a2,a1), a1) ≡ a2 by add_then_sub_cancel(a2, a1)
                    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                        DynTowerSpec>(a2, a1);
                    lemma_dts_eqv_symmetric(dts_sub(dts_add(a2, a1), a1), a2);
                    // sub(sum_re, a1) ≡ sub(add(a2,a1), a1) by sub_congruence from commutative
                    // Actually, sub(add(a1,a2), a1) and sub(add(a2,a1), a1) differ.
                    // sub(add(a1,a2), a1) = add(add(a1,a2), neg(a1)).
                    // sub(add(a2,a1), a1) = add(add(a2,a1), neg(a1)).
                    // eqv follows from add_congruence_left(add(a1,a2), add(a2,a1), neg(a1)).
                    lemma_dts_add_congruence_left(
                        dts_add(a1, a2), dts_add(a2, a1), dts_neg(a1));
                    // eqv(sub(sum_re, a1), sub(add(a2,a1), a1))
                    // chain: p = a2 ≡ sub(add(a2,a1),a1) ≡ sub(add(a1,a2), a1) = sub(sum_re, r)
                    lemma_dts_eqv_symmetric(
                        dts_sub(dts_add(a1, a2), a1),
                        dts_sub(dts_add(a2, a1), a1));
                    lemma_dts_eqv_transitive(
                        a2, dts_sub(dts_add(a2, a1), a1),
                        dts_sub(dts_add(a1, a2), a1));
                }
                lemma_dts_nonneg_fuel_congruence(p, dts_sub(sum_re, r), f);
                // difference_of_squares(r, sum_re)
                lemma_dts_same_radicand_symmetric(r, sum_re);
                lemma_dts_difference_of_squares(r, sum_re);
                // nonneg(add(sum_re, r)) by nonneg_add IH (both nonneg)
                lemma_dts_nonneg_add_closed_fuel(sum_re, r, f);
                // nonneg(mul(sub(sum_re,r), add(sum_re,r))) by nonneg_mul IH
                lemma_dts_add_closed(sum_re, r);
                lemma_dts_same_radicand_symmetric(sum_re, dts_add(sum_re, r));
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re, r), sum_re, dts_add(sum_re, r));
                lemma_dts_nonneg_radicands_add(sum_re, r);
                lemma_dts_depth_add_le(sum_re, r);
                lemma_dts_nonneg_mul_closed_fuel(
                    dts_sub(sum_re, r), dts_add(sum_re, r), f);
                // Transfer: mul(sub,add) ≡ sub(sum_re², r²) → nonneg(sub(sum_re², r²))
                lemma_dts_mul_closed(sum_re, sum_re);
                lemma_dts_mul_closed(r, r);
                lemma_dts_mul_closed(dts_sub(sum_re, r), dts_add(sum_re, r));
                lemma_dts_same_radicand_symmetric(sum_re, dts_mul(sum_re, sum_re));
                lemma_dts_same_radicand_transitive(dts_mul(sum_re, sum_re), sum_re, r);
                lemma_dts_same_radicand_symmetric(r, dts_mul(r, r));
                lemma_dts_same_radicand_transitive(dts_mul(sum_re, sum_re), r, dts_mul(r, r));
                lemma_dts_same_radicand_neg(dts_mul(r, r));
                lemma_dts_same_radicand_transitive(
                    dts_mul(sum_re, sum_re), dts_mul(r, r), dts_neg(dts_mul(r, r)));
                lemma_dts_neg_well_formed(dts_mul(r, r));
                lemma_dts_add_closed(dts_mul(sum_re, sum_re), dts_neg(dts_mul(r, r)));
                lemma_dts_same_radicand_symmetric(
                    dts_sub(sum_re, r), dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
                    dts_sub(sum_re, r), sum_re);
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
                    sum_re, sum_re_sq);
                lemma_dts_same_radicand_symmetric(
                    sum_re_sq, dts_sub(sum_re_sq, r_sq));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
                    sum_re_sq, dts_sub(sum_re_sq, r_sq));
                lemma_dts_eqv_symmetric(dts_sub(sum_re_sq, r_sq),
                    dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)));
                lemma_dts_nonneg_fuel_congruence(
                    dts_mul(dts_sub(sum_re, r), dts_add(sum_re, r)),
                    dts_sub(sum_re_sq, r_sq), f);
                // T1 done: nonneg(sub(sum_re², r²), f) ✓

                // ── T2: r² ≥ d*s² (given from C2 norm bound) ──
                // From nonneg_fuel(y, fuel) or nonneg_fuel(x, fuel) C2 case,
                // Z3 should extract this. It's a direct sub-expression of nonneg_fuel.

                // ── Chain T1+T2: sub_add_sub + nonneg_add IH ──
                let d_s_sq = dts_mul(dd, s_sq);
                lemma_dts_mul_closed(s, s);
                lemma_dts_same_radicand_symmetric(a1, dd);
                lemma_dts_same_radicand_transitive(dd, a1, b1);
                lemma_dts_same_radicand_transitive(dd, b1, s);
                lemma_dts_same_radicand_symmetric(s, dts_mul(s, s));
                lemma_dts_same_radicand_transitive(dd, s, s_sq);
                lemma_dts_mul_closed(dd, s_sq);
                lemma_dts_nonneg_radicands_mul(s, s);
                lemma_dts_nonneg_radicands_mul(dd, s_sq);
                // sub_add_sub(sum_re², r², d*s²)
                verus_algebra::lemmas::additive_group_lemmas::lemma_sub_add_sub::<DynTowerSpec>(
                    sum_re_sq, r_sq, d_s_sq);
                // nonneg_add(sub(sum_re²,r²), sub(r²,d*s²)) at fuel f
                lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, r_sq));
                lemma_dts_neg_well_formed(d_s_sq);
                lemma_dts_same_radicand_neg(d_s_sq);
                lemma_dts_same_radicand_symmetric(dd, d_s_sq);
                lemma_dts_same_radicand_transitive(r_sq, r, dd);
                lemma_dts_same_radicand_symmetric(r, r_sq);
                lemma_dts_same_radicand_transitive(r_sq, dd, d_s_sq);
                lemma_dts_same_radicand_transitive(r_sq, d_s_sq, dts_neg(d_s_sq));
                lemma_dts_add_closed(r_sq, dts_neg(d_s_sq));
                lemma_dts_same_radicand_symmetric(r_sq, dts_sub(r_sq, d_s_sq));
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), sum_re_sq, sum_re);
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), sum_re, r);
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), r, r_sq);
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), r_sq, dts_sub(r_sq, d_s_sq));
                lemma_dts_nonneg_radicands_mul(sum_re, sum_re);
                lemma_dts_nonneg_radicands_mul(r, r);
                lemma_dts_nonneg_radicands_neg(r_sq);
                lemma_dts_nonneg_radicands_add(sum_re_sq, dts_neg(r_sq));
                lemma_dts_nonneg_radicands_neg(d_s_sq);
                lemma_dts_nonneg_radicands_add(r_sq, dts_neg(d_s_sq));
                lemma_dts_depth_mul_le(sum_re, sum_re);
                lemma_dts_depth_mul_le(r, r);
                lemma_dts_depth_mul_le(dd, s_sq);
                lemma_dts_depth_neg(r_sq);
                lemma_dts_depth_add_le(sum_re_sq, dts_neg(r_sq));
                lemma_dts_depth_neg(d_s_sq);
                lemma_dts_depth_add_le(r_sq, dts_neg(d_s_sq));
                // ── Chain T1+T2 → nonneg(sub(sum_re², d*s²)) ──
                // same_radicand chains for intermediate terms
                lemma_dts_mul_closed(sum_re, sum_re);
                lemma_dts_mul_closed(r, r);
                lemma_dts_same_radicand_symmetric(sum_re, sum_re_sq);
                lemma_dts_same_radicand_transitive(sum_re_sq, sum_re, r);
                lemma_dts_same_radicand_symmetric(r, r_sq);
                lemma_dts_same_radicand_transitive(sum_re_sq, r, r_sq);
                lemma_dts_same_radicand_neg(r_sq);
                lemma_dts_same_radicand_transitive(sum_re_sq, r_sq, dts_neg(r_sq));
                lemma_dts_neg_well_formed(r_sq);
                lemma_dts_add_closed(sum_re_sq, dts_neg(r_sq));
                // r_sq ~ dd ~ d_s_sq chain
                lemma_dts_same_radicand_transitive(r_sq, r, dd);
                lemma_dts_same_radicand_symmetric(dd, d_s_sq);
                lemma_dts_same_radicand_transitive(r_sq, dd, d_s_sq);
                lemma_dts_same_radicand_neg(d_s_sq);
                lemma_dts_same_radicand_transitive(r_sq, d_s_sq, dts_neg(d_s_sq));
                lemma_dts_neg_well_formed(d_s_sq);
                lemma_dts_add_closed(r_sq, dts_neg(d_s_sq));
                // same_radicand between the two sub terms
                lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, r_sq));
                lemma_dts_same_radicand_symmetric(r_sq, dts_sub(r_sq, d_s_sq));
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), sum_re_sq, r_sq);
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, r_sq), r_sq, dts_sub(r_sq, d_s_sq));
                // nonneg_radicands for sub terms
                lemma_dts_nonneg_radicands_mul(sum_re, sum_re);
                lemma_dts_nonneg_radicands_mul(r, r);
                lemma_dts_nonneg_radicands_neg(r_sq);
                lemma_dts_nonneg_radicands_add(sum_re_sq, dts_neg(r_sq));
                lemma_dts_nonneg_radicands_neg(d_s_sq);
                lemma_dts_nonneg_radicands_add(r_sq, dts_neg(d_s_sq));
                // depth bounds for all intermediate terms
                lemma_dts_depth_mul_le(sum_re, sum_re);
                lemma_dts_depth_mul_le(r, r);
                lemma_dts_depth_mul_le(s, s);
                lemma_dts_depth_mul_le(dd, s_sq);
                lemma_dts_depth_neg(r_sq);
                lemma_dts_depth_add_le(sum_re_sq, dts_neg(r_sq));
                lemma_dts_depth_neg(d_s_sq);
                lemma_dts_depth_add_le(r_sq, dts_neg(d_s_sq));
                // Ghost var depth hints for Z3
                assert(dts_depth(r) <= dts_depth(a1) || dts_depth(r) <= dts_depth(a2));
                assert(dts_depth(s) <= dts_depth(b1) || dts_depth(s) <= dts_depth(b2));
                // T2: nonneg(sub(r_sq, d_s_sq), f) from C2 norm bound
                assert(dts_nonneg_fuel(dts_sub(r_sq, d_s_sq), f));
                // nonneg_add(T1, T2) → nonneg(sub(sum_re², d*s²))
                lemma_dts_nonneg_add_closed_fuel(
                    dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq), f);
                // Transfer via sub_add_sub: T1+T2 ≡ sub(sum_re², d*s²)
                lemma_dts_add_closed(
                    dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq));
                lemma_dts_same_radicand_symmetric(
                    dts_sub(sum_re_sq, r_sq),
                    dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)));
                lemma_dts_same_radicand_transitive(sum_re_sq, r_sq, d_s_sq);
                lemma_dts_same_radicand_transitive(sum_re_sq, d_s_sq, dts_neg(d_s_sq));
                lemma_dts_add_closed(sum_re_sq, dts_neg(d_s_sq));
                lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, d_s_sq));
                lemma_dts_same_radicand_transitive(
                    dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
                    dts_sub(sum_re_sq, r_sq), sum_re_sq);
                lemma_dts_same_radicand_transitive(
                    dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
                    sum_re_sq, dts_sub(sum_re_sq, d_s_sq));
                lemma_dts_nonneg_fuel_congruence(
                    dts_add(dts_sub(sum_re_sq, r_sq), dts_sub(r_sq, d_s_sq)),
                    dts_sub(sum_re_sq, d_s_sq), f);
                // nonneg(sub(sum_re², d*s²)) at fuel f ✓

                // ── T3: d*s² ≥ d*(b1+b2)² ──
                // (b1+b2)² ≤ s²: |b1+b2| ≤ |s| since q ≥ 0 reduces magnitude
                // neg(sum_im) ≤ neg(s): sub(neg(s), neg(sum_im)) ≡ q by add_sub_cancel_right
                // square_le_square on neg: neg(sum_im)² ≤ neg(s)²
                // neg_mul_neg: neg(x)² ≡ x² → (b1+b2)² ≤ s²
                // Multiply by d ≥ 0: d*(b1+b2)² ≤ d*s²
                // i.e. nonneg(sub(d*s², d*sum_im²))
                //
                // This step is another inline difference_of_squares + nonneg_mul chain.
                // For brevity, use distributes: d*(s²-(b1+b2)²) ≡ d*s²-d*(b1+b2)²
                // And s²-(b1+b2)² ≡ (s-(b1+b2))(s+(b1+b2)) via difference_of_squares
                // All at fuel f using IH.
                //
                // For now: this final step mirrors T1. TODO for next session.
                // The chain sum_re² ≥ d*s² is already proved above.
                // We also need sum_re² ≥ d*sum_im².
                // If d*sum_im² ≤ d*s² ≤ sum_re²: done by transitivity.
                // ── T3: nonneg(sub(d*s², d*sum_im²), f) ──
                // neg(sum_im) ≤ neg(s): sub(neg(s), neg(sum_im)) ≡ q. nonneg(q) ✓.
                let ns = dts_neg(s);
                let nsm = dts_neg(sum_im);
                lemma_dts_neg_well_formed(s);
                lemma_dts_neg_well_formed(sum_im);
                lemma_dts_same_radicand_neg(s);
                lemma_dts_same_radicand_neg(sum_im);
                lemma_dts_same_radicand_symmetric(s, ns);
                lemma_dts_same_radicand_symmetric(sum_im, nsm);
                // same_radicand(s, sum_im): s ∈ {b1,b2}, sum_im = add(b1,b2)
                lemma_dts_same_radicand_symmetric(b1, b2);
                lemma_dts_same_radicand_transitive(b2, b1, dts_add(b1, b2));
                // Now Z3 has sr(b1, sum_im) and sr(b2, sum_im), so sr(s, sum_im) ✓
                lemma_dts_same_radicand_transitive(ns, s, sum_im);
                lemma_dts_same_radicand_transitive(ns, sum_im, nsm);
                lemma_dts_nonneg_radicands_neg(s);
                lemma_dts_nonneg_radicands_add(b1, b2);
                lemma_dts_nonneg_radicands_neg(sum_im);
                lemma_dts_depth_neg(s);
                lemma_dts_depth_neg(sum_im);
                // nonneg(neg(s)): from C2 nonneg case (neg of the C2 im)
                // nonneg(neg(sum_im)): from le_total (we're in !nonneg(sum_im) branch)
                // sub(neg(s), neg(sum_im)) ≡ q by additive algebra
                // nonneg(sub(neg(s), neg(sum_im))) from nonneg(q)
                lemma_dts_same_radicand_symmetric(ns, nsm);
                lemma_dts_neg_well_formed(nsm);
                lemma_dts_same_radicand_neg(nsm);
                lemma_dts_same_radicand_transitive(ns, nsm, dts_neg(nsm));
                lemma_dts_add_closed(ns, dts_neg(nsm));
                lemma_dts_nonneg_radicands_neg(nsm);
                lemma_dts_nonneg_radicands_add(ns, dts_neg(nsm));
                lemma_dts_depth_neg(nsm);
                lemma_dts_depth_add_le(ns, dts_neg(nsm));
                verus_algebra::lemmas::additive_group_lemmas::lemma_add_sub_cancel_right::<
                    DynTowerSpec>(ns, nsm, s);
                // sub(ns, nsm) = (neg(s)+s)-(neg(sum_im)+s) ≡ ... hmm, not directly useful.
                // Simpler: add_sub_cancel_right(q, neg_q_complement, s) doesn't help.
                // Use direct: neg(s)-neg(sum_im) = neg(s)+sum_im (by neg_involution on neg(sum_im))
                lemma_dts_neg_involution(sum_im);
                // neg(neg(sum_im)) ≡ sum_im. sub(neg(s), neg(sum_im)) = add(neg(s), neg(neg(sum_im))) ≡ add(neg(s), sum_im)
                // If b1_nn: add(neg(b2), add(b1,b2)) ≡ b1 = q
                // If !b1_nn: add(neg(b1), add(b1,b2)) ≡ b2 = q
                // In both cases ≡ q. nonneg(q) ✓.
                // Let Z3 derive this from neg_involution + additive algebra
                let q = if b1_nn { b1 } else { b2 };
                lemma_dts_same_radicand_symmetric(ns, dts_sub(ns, nsm));
                lemma_dts_same_radicand_transitive(q, s, ns);
                lemma_dts_same_radicand_symmetric(s, q);
                lemma_dts_same_radicand_transitive(q, ns, dts_sub(ns, nsm));
                lemma_dts_same_radicand_symmetric(q, dts_sub(ns, nsm));
                // Prove eqv(q, sub(ns, nsm)):
                // sub(ns,nsm) = add(neg(s), neg(neg(sum_im))) ≡ add(neg(s), sum_im) [neg_involution]
                // ≡ sub(sum_im, s) [by add_commutative + sub def]
                // ≡ q [by add_then_sub_cancel(q, s_complement)]
                lemma_dts_neg_involution(sum_im);
                DynTowerSpec::axiom_add_commutative(dts_neg(s), sum_im);
                if b1_nn {
                    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                        DynTowerSpec>(b1, b2);
                } else {
                    DynTowerSpec::axiom_add_commutative(b1, b2);
                    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                        DynTowerSpec>(b2, b1);
                }
                // Explicit eqv chain: q ≡ sub(sum_im, s) ≡ sub(ns, nsm)
                // sub(ns, nsm) = add(neg(s), neg(neg(sum_im)))
                // neg(neg(sum_im)) ≡ sum_im → add_congruence → add(neg(s), sum_im)
                // add(neg(s), sum_im) ≡ add(sum_im, neg(s)) = sub(sum_im, s) ≡ q
                lemma_dts_add_congruence_right(
                    dts_neg(s), dts_neg(nsm), sum_im);
                // Chain: sub(ns,nsm) ≡ add(neg(s),sum_im) ≡ sub(sum_im,s) ≡ q
                // Chain sub(ns,nsm) → add(neg(s),sum_im) → sub(sum_im,s) → q
                DynTowerSpec::axiom_add_commutative(dts_neg(s), sum_im);
                lemma_dts_eqv_transitive(
                    dts_sub(ns, nsm),
                    dts_add(dts_neg(s), sum_im),
                    dts_sub(sum_im, s));
                // eqv(q, sub(sum_im, s)): from add_then_sub + congruence
                if !b1_nn {
                    // Need: sub(add(b1,b2), b1) ≡ sub(add(b2,b1), b1) ≡ b2
                    lemma_dts_add_congruence_left(
                        dts_add(b1, b2), dts_add(b2, b1), dts_neg(b1));
                }
                // eqv(sub(sum_im, s), q): Z3 has add_then_sub + commutative facts
                // For b1_nn: sub(add(b1,b2), b2) ≡ b1 = q. sum_im=add(b1,b2), s=b2. ✓
                // For !b1_nn: sub(add(b1,b2), b1) ≡ b2 = q via commutative chain. ✓
                // eqv(sub(sum_im, s), q): explicit for both branches
                if b1_nn {
                    // sub(add(b1,b2), b2) ≡ b1 = q
                    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                        DynTowerSpec>(b1, b2);
                } else {
                    // sub(add(b1,b2), b1): commutative + cancel
                    DynTowerSpec::axiom_add_commutative(b1, b2);
                    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<
                        DynTowerSpec>(b2, b1);
                    lemma_dts_add_congruence_left(
                        dts_add(b1, b2), dts_add(b2, b1), dts_neg(b1));
                }
                lemma_dts_eqv_symmetric(q, dts_sub(sum_im, s));
                lemma_dts_eqv_transitive(dts_sub(ns, nsm), dts_sub(sum_im, s), q);
                lemma_dts_eqv_symmetric(dts_sub(ns, nsm), q);
                lemma_dts_nonneg_fuel_congruence(q, dts_sub(ns, nsm), f);
                // Inline square_le_square(neg(sum_im), neg(s)):
                // difference_of_squares(nsm, ns): sub(ns², nsm²) ≡ mul(sub(ns,nsm), add(ns,nsm))
                lemma_dts_same_radicand_symmetric(nsm, ns);
                lemma_dts_difference_of_squares(nsm, ns);
                // nonneg(add(ns, nsm)): both nonneg → nonneg_add IH
                lemma_dts_nonneg_add_closed_fuel(ns, nsm, f);
                // nonneg(mul(sub(ns,nsm), add(ns,nsm))): nonneg_mul IH
                lemma_dts_add_closed(ns, nsm);
                lemma_dts_same_radicand_symmetric(ns, dts_add(ns, nsm));
                lemma_dts_same_radicand_transitive(
                    dts_sub(ns, nsm), ns, dts_add(ns, nsm));
                lemma_dts_nonneg_radicands_add(ns, nsm);
                lemma_dts_depth_add_le(ns, nsm);
                lemma_dts_nonneg_mul_closed_fuel(
                    dts_sub(ns, nsm), dts_add(ns, nsm), f);
                // congruence: mul(...) ≡ sub(ns², nsm²) → nonneg(sub(ns², nsm²))
                let ns_sq = dts_mul(ns, ns);
                let nsm_sq = dts_mul(nsm, nsm);
                lemma_dts_same_radicand_reflexive(ns);
                lemma_dts_same_radicand_reflexive(nsm);
                lemma_dts_mul_closed(ns, ns);
                lemma_dts_mul_closed(nsm, nsm);
                lemma_dts_mul_closed(dts_sub(ns, nsm), dts_add(ns, nsm));
                lemma_dts_same_radicand_reflexive(ns);
                lemma_dts_same_radicand_reflexive(nsm);
                lemma_dts_same_radicand_symmetric(ns, ns_sq);
                lemma_dts_same_radicand_transitive(ns_sq, ns, nsm);
                lemma_dts_same_radicand_symmetric(nsm, nsm_sq);
                lemma_dts_same_radicand_transitive(ns_sq, nsm, nsm_sq);
                lemma_dts_same_radicand_neg(nsm_sq);
                lemma_dts_same_radicand_transitive(ns_sq, nsm_sq, dts_neg(nsm_sq));
                lemma_dts_neg_well_formed(nsm_sq);
                lemma_dts_add_closed(ns_sq, dts_neg(nsm_sq));
                lemma_dts_same_radicand_symmetric(
                    dts_sub(ns, nsm),
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)),
                    dts_sub(ns, nsm), ns);
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)),
                    ns, ns_sq);
                lemma_dts_same_radicand_symmetric(ns_sq, dts_sub(ns_sq, nsm_sq));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)),
                    ns_sq, dts_sub(ns_sq, nsm_sq));
                lemma_dts_eqv_symmetric(dts_sub(ns_sq, nsm_sq),
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)));
                lemma_dts_nonneg_fuel_congruence(
                    dts_mul(dts_sub(ns, nsm), dts_add(ns, nsm)),
                    dts_sub(ns_sq, nsm_sq), f);
                // nonneg(sub(neg(s)², neg(sum_im)²)) ✓
                // Transfer to nonneg(sub(s², sum_im²)) via neg_mul_neg congruence
                lemma_dts_neg_mul_neg(s, s);
                lemma_dts_neg_mul_neg(sum_im, sum_im);
                // same_radicand chains: ns_sq ~ ns ~ s ~ s_sq, nsm_sq ~ nsm ~ sum_im ~ sum_im_sq
                lemma_dts_mul_closed(s, s);
                lemma_dts_mul_closed(sum_im, sum_im);
                lemma_dts_same_radicand_symmetric(ns, ns_sq);
                lemma_dts_same_radicand_transitive(ns_sq, ns, s);
                lemma_dts_same_radicand_symmetric(s, s_sq);
                lemma_dts_same_radicand_transitive(ns_sq, s, s_sq);
                lemma_dts_same_radicand_symmetric(nsm, nsm_sq);
                lemma_dts_same_radicand_transitive(nsm_sq, nsm, sum_im);
                lemma_dts_same_radicand_symmetric(sum_im, sum_im_sq);
                lemma_dts_same_radicand_transitive(nsm_sq, sum_im, sum_im_sq);
                lemma_dts_sub_congruence_both(ns_sq, nsm_sq, s_sq, sum_im_sq);
                lemma_dts_same_radicand_symmetric(
                    dts_sub(ns_sq, nsm_sq), dts_sub(s_sq, sum_im_sq));
                // Hmm, sub_congruence_both(ns_sq, nsm_sq, s_sq, sum_im_sq) gives
                // eqv(sub(ns_sq, nsm_sq), sub(s_sq, sum_im_sq)) AND same_radicand.
                lemma_dts_nonneg_fuel_congruence(
                    dts_sub(ns_sq, nsm_sq), dts_sub(s_sq, sum_im_sq), f);
                // nonneg(sub(s², sum_im²)) ✓

                // d * (s² - sum_im²) ≥ 0: nonneg_mul IH on d and sub(s², sum_im²)
                lemma_dts_nonneg_radicands_mul(s, s);
                lemma_dts_nonneg_radicands_mul(sum_im, sum_im);
                lemma_dts_nonneg_radicands_neg(sum_im_sq);
                lemma_dts_nonneg_radicands_add(s_sq, dts_neg(sum_im_sq));
                lemma_dts_same_radicand_symmetric(s, s_sq);
                lemma_dts_same_radicand_transitive(dd, s, s_sq);
                lemma_dts_same_radicand_transitive(s_sq, s, sum_im);
                lemma_dts_same_radicand_symmetric(sum_im, sum_im_sq);
                lemma_dts_same_radicand_transitive(s_sq, sum_im, sum_im_sq);
                lemma_dts_same_radicand_neg(sum_im_sq);
                lemma_dts_same_radicand_transitive(s_sq, sum_im_sq, dts_neg(sum_im_sq));
                lemma_dts_neg_well_formed(sum_im_sq);
                lemma_dts_add_closed(s_sq, dts_neg(sum_im_sq));
                lemma_dts_same_radicand_symmetric(s_sq, dts_sub(s_sq, sum_im_sq));
                lemma_dts_same_radicand_transitive(dd, s_sq, dts_sub(s_sq, sum_im_sq));
                lemma_dts_depth_mul_le(s, s);
                lemma_dts_depth_mul_le(sum_im, sum_im);
                lemma_dts_depth_neg(sum_im_sq);
                lemma_dts_depth_add_le(s_sq, dts_neg(sum_im_sq));
                lemma_dts_nonneg_radicands_mul(s, s);
                lemma_dts_nonneg_radicands_mul(sum_im, sum_im);
                lemma_dts_nonneg_radicands_neg(sum_im_sq);
                lemma_dts_nonneg_radicands_add(s_sq, dts_neg(sum_im_sq));
                // nonneg(d) at fuel f for multiplication
                lemma_dts_nonneg_fuel_stabilize(dd, f);
                lemma_dts_nonneg_mul_closed_fuel(dd, dts_sub(s_sq, sum_im_sq), f);
                // mul(d, sub(s², sum_im²)) ≡ sub(d*s², d*sum_im²) via distributes + neg_mul_right
                let d_sum_im_sq = dts_mul(dd, sum_im_sq);
                lemma_dts_mul_distributes_left(dd, s_sq, dts_neg(sum_im_sq));
                lemma_dts_same_radicand_transitive(dd, s, sum_im);
                lemma_dts_same_radicand_transitive(dd, sum_im, sum_im_sq);
                lemma_dts_neg_mul_right(dd, sum_im_sq);
                lemma_dts_add_congruence_right(
                    dts_mul(dd, s_sq), dts_mul(dd, dts_neg(sum_im_sq)),
                    dts_neg(d_sum_im_sq));
                lemma_dts_eqv_transitive(
                    dts_mul(dd, dts_sub(s_sq, sum_im_sq)),
                    dts_add(dts_mul(dd, s_sq), dts_mul(dd, dts_neg(sum_im_sq))),
                    dts_add(d_s_sq, dts_neg(d_sum_im_sq)));
                // Transfer nonneg: mul(d, sub(s²,sum_im²)) → sub(d*s², d*sum_im²)
                lemma_dts_mul_closed(dd, sum_im_sq);
                lemma_dts_neg_well_formed(d_sum_im_sq);
                lemma_dts_same_radicand_symmetric(dd, d_s_sq);
                lemma_dts_same_radicand_symmetric(dd, d_sum_im_sq);
                lemma_dts_same_radicand_transitive(d_s_sq, dd, d_sum_im_sq);
                lemma_dts_same_radicand_neg(d_sum_im_sq);
                lemma_dts_same_radicand_transitive(d_s_sq, d_sum_im_sq, dts_neg(d_sum_im_sq));
                lemma_dts_add_closed(d_s_sq, dts_neg(d_sum_im_sq));
                lemma_dts_mul_closed(dd, dts_sub(s_sq, sum_im_sq));
                lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_sub(s_sq, sum_im_sq)));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dd, dts_sub(s_sq, sum_im_sq)), dd, d_s_sq);
                lemma_dts_same_radicand_symmetric(d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
                lemma_dts_same_radicand_transitive(
                    dts_mul(dd, dts_sub(s_sq, sum_im_sq)), d_s_sq,
                    dts_sub(d_s_sq, d_sum_im_sq));
                lemma_dts_nonneg_fuel_congruence(
                    dts_mul(dd, dts_sub(s_sq, sum_im_sq)),
                    dts_sub(d_s_sq, d_sum_im_sq), f);
                // nonneg(sub(d*s², d*sum_im²)) ✓ = T3

                // ── Final chain: T1+T2+T3 → nonneg(sub(sum_re², d*sum_im²)) ──
                verus_algebra::lemmas::additive_group_lemmas::lemma_sub_add_sub::<DynTowerSpec>(
                    sum_re_sq, d_s_sq, d_sum_im_sq);
                lemma_dts_same_radicand_symmetric(d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, d_s_sq), sum_re_sq, d_s_sq);
                lemma_dts_same_radicand_transitive(
                    dts_sub(sum_re_sq, d_s_sq), d_s_sq, dts_sub(d_s_sq, d_sum_im_sq));
                lemma_dts_nonneg_radicands_mul(dd, sum_im_sq);
                lemma_dts_nonneg_radicands_neg(d_sum_im_sq);
                lemma_dts_nonneg_radicands_add(d_s_sq, dts_neg(d_sum_im_sq));
                lemma_dts_nonneg_radicands_add(sum_re_sq, dts_neg(d_s_sq));
                lemma_dts_depth_neg(d_sum_im_sq);
                lemma_dts_depth_add_le(d_s_sq, dts_neg(d_sum_im_sq));
                lemma_dts_nonneg_add_closed_fuel(
                    dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq), f);
                // Transfer: sub(sum_re²,d*s²) + sub(d*s²,d*sum_im²) ≡ sub(sum_re²,d*sum_im²)
                lemma_dts_add_closed(
                    dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq));
                lemma_dts_same_radicand_transitive(sum_re_sq, d_s_sq, d_sum_im_sq);
                lemma_dts_same_radicand_neg(d_sum_im_sq);
                lemma_dts_same_radicand_transitive(sum_re_sq, d_sum_im_sq, dts_neg(d_sum_im_sq));
                lemma_dts_add_closed(sum_re_sq, dts_neg(d_sum_im_sq));
                lemma_dts_same_radicand_symmetric(
                    dts_sub(sum_re_sq, d_s_sq),
                    dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)));
                lemma_dts_same_radicand_symmetric(sum_re_sq, dts_sub(sum_re_sq, d_sum_im_sq));
                lemma_dts_same_radicand_transitive(
                    dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
                    dts_sub(sum_re_sq, d_s_sq), sum_re_sq);
                lemma_dts_same_radicand_transitive(
                    dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
                    sum_re_sq, dts_sub(sum_re_sq, d_sum_im_sq));
                lemma_dts_nonneg_fuel_congruence(
                    dts_add(dts_sub(sum_re_sq, d_s_sq), dts_sub(d_s_sq, d_sum_im_sq)),
                    dts_sub(sum_re_sq, d_sum_im_sq), f);
                // nonneg(sub(sum_re², d*sum_im²)) at fuel f ✓ — the norm bound!
                return;
            } // end if false (dead code — old inline norm bound, now in helper)
            // TODO: C1+C3, C3+C1, C2+C2, C2+C3, C3+C2, C3+C3
        }
        _ => {}
    }
}

/// Nonneg closed under multiplication. Mutually recursive with nonneg_add_closed.
pub proof fn lemma_dts_nonneg_mul_closed_fuel(
    x: DynTowerSpec, y: DynTowerSpec, fuel: nat,
)
    requires
        fuel >= dts_depth(x) + 1, fuel >= dts_depth(y) + 1,
        dts_well_formed(x), dts_well_formed(y),
        dts_same_radicand(x, y),
        dts_nonneg_radicands(x), dts_nonneg_radicands(y),
        dts_nonneg_fuel(x, fuel), dts_nonneg_fuel(y, fuel),
    ensures
        dts_nonneg_fuel(dts_mul(x, y), fuel),
    decreases fuel, 0nat,
{
    match (x, y) {
        (DynTowerSpec::Rat(r1), DynTowerSpec::Rat(r2)) => {
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<
                Rational>(r1, r2);
        }
        (DynTowerSpec::Ext(re1, im1, d), DynTowerSpec::Ext(re2, im2, _)) => {
            let f = (fuel - 1) as nat;
            let a1 = *re1; let b1 = *im1; let dd = *d;
            let a2 = *re2; let b2 = *im2;
            lemma_dts_depth_mul_le(a1, a2);
            lemma_dts_depth_mul_le(b1, b2);
            lemma_dts_depth_mul_le(a1, b2);
            lemma_dts_depth_mul_le(b1, a2);
            lemma_dts_depth_mul_le(dd, dts_mul(b1, b2));
            lemma_dts_depth_add_le(
                dts_mul(a1, a2), dts_mul(dd, dts_mul(b1, b2)));
            lemma_dts_depth_add_le(
                dts_mul(a1, b2), dts_mul(b1, a2));
            // Cross same_radicand
            lemma_dts_same_radicand_transitive(a1, b1, b2);
            lemma_dts_same_radicand_symmetric(a1, b1);
            lemma_dts_same_radicand_transitive(b1, a1, a2);
            lemma_dts_same_radicand_symmetric(a1, dd);
            lemma_dts_same_radicand_transitive(dd, a1, b1);
            let a1_nn = dts_nonneg_fuel(a1, f);
            let b1_nn = dts_nonneg_fuel(b1, f);
            let a2_nn = dts_nonneg_fuel(a2, f);
            let b2_nn = dts_nonneg_fuel(b2, f);

            // C1×C1: all sub-components nonneg → all products nonneg → result C1
            if a1_nn && b1_nn && a2_nn && b2_nn {
                // well_formed + radicand chains for products
                lemma_dts_mul_closed(b1, b2);
                lemma_dts_mul_closed(a1, b2);
                lemma_dts_mul_closed(b1, a2);
                lemma_dts_mul_closed(a1, a2);
                lemma_dts_nonneg_radicands_mul(a1, a2);
                lemma_dts_nonneg_radicands_mul(b1, b2);
                lemma_dts_nonneg_radicands_mul(a1, b2);
                lemma_dts_nonneg_radicands_mul(b1, a2);
                // nonneg of sub-products by IH
                lemma_dts_nonneg_mul_closed_fuel(a1, a2, f);
                lemma_dts_nonneg_mul_closed_fuel(b1, b2, f);
                lemma_dts_nonneg_mul_closed_fuel(a1, b2, f);
                lemma_dts_nonneg_mul_closed_fuel(b1, a2, f);
                // d * b1*b2: nonneg(d) from nonneg_radicands, nonneg(b1*b2) from IH
                lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, b2));
                lemma_dts_same_radicand_transitive(dd, b1, dts_mul(b1, b2));
                lemma_dts_mul_closed(dd, dts_mul(b1, b2));
                lemma_dts_nonneg_radicands_mul(dd, dts_mul(b1, b2));
                lemma_dts_nonneg_fuel_stabilize(dd, f);
                lemma_dts_nonneg_mul_closed_fuel(dd, dts_mul(b1, b2), f);
                // re = a1*a2 + d*b1*b2: sum of nonneg by IH
                lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, a2));
                lemma_dts_same_radicand_symmetric(dd, dts_mul(dd, dts_mul(b1, b2)));
                lemma_dts_same_radicand_transitive(
                    dts_mul(a1, a2), a1, dd);
                lemma_dts_same_radicand_transitive(
                    dts_mul(a1, a2), dd, dts_mul(dd, dts_mul(b1, b2)));
                lemma_dts_nonneg_radicands_add(
                    dts_mul(a1, a2), dts_mul(dd, dts_mul(b1, b2)));
                lemma_dts_nonneg_add_closed_fuel(
                    dts_mul(a1, a2), dts_mul(dd, dts_mul(b1, b2)), f);
                // im = a1*b2 + b1*a2: sum of nonneg by IH
                lemma_dts_same_radicand_symmetric(a1, dts_mul(a1, b2));
                lemma_dts_same_radicand_symmetric(b1, dts_mul(b1, a2));
                lemma_dts_same_radicand_transitive(
                    dts_mul(a1, b2), a1, b1);
                lemma_dts_same_radicand_transitive(
                    dts_mul(a1, b2), b1, dts_mul(b1, a2));
                lemma_dts_nonneg_radicands_add(
                    dts_mul(a1, b2), dts_mul(b1, a2));
                lemma_dts_nonneg_add_closed_fuel(
                    dts_mul(a1, b2), dts_mul(b1, a2), f);
                return;
            }
            // TODO: remaining nonneg_mul cases (B×B, A×A non-C1, A×B, B×A)
            // All need norm_mul: norm(xy) ≡ norm(x)·norm(y)
        }
        _ => {}
    }
}

} // verus!
