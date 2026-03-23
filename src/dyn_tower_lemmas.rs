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
    // add produces: Rat+Rat=Rat, Ext+Ext=Ext(add re, add im, d from first),
    // Rat+Ext=Ext, Ext+Rat=Ext.
    // same_radicand checks: Rat×Rat=true, Ext×Ext: d1==d2 && recursive, cross=true.
    // Key: add(a1,b1) and add(a2,b2) use d from FIRST arg (a1 or a2).
    // If same_radicand(a1,a2) and both Ext: d_a1==d_a2.
    // Result both Ext with d from a1/a2 respectively → same.
    match (a1, a2, b1, b2) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {},
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _), DynTowerSpec::Ext(re_b2, im_b2, _)) => {
            // add(Rat, Ext_b1) = Ext(add(Rat, re_b1), im_b1, d_b1)
            // add(Rat, Ext_b2) = Ext(add(Rat, re_b2), im_b2, d_b2)
            // same_radicand(b1, b2): d_b1 == d_b2 ✓
            // re: same_radicand(add(Rat_a1, re_b1), add(Rat_a2, re_b2))
            // These are just Rat+something, always Rat or Ext depending on re_b.
            // Actually add(Rat(r), Ext(re,im,d)) = Ext(add(Rat(r), re), im, d)
            // So result is always Ext with d from b. Both have same d. ✓
            // sub: same_radicand(add(Rat_a1, re_b1), add(Rat_a2, re_b2)) — recurse
            let ra1 = match a1 { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            let ra2 = match a2 { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            let (re_b1, im_b1) = match b1 { DynTowerSpec::Ext(re, im, _) => (*re, *im), _ => arbitrary() };
            lemma_dts_add_preserves_same_radicand_both(
                DynTowerSpec::Rat(ra1), DynTowerSpec::Rat(ra2), re_b1, *re_b2);
        },
        (DynTowerSpec::Ext(re_a1, im_a1, _), DynTowerSpec::Ext(re_a2, im_a2, _),
         DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {
            // add(Ext_a1, Rat_b1) = Ext(add(re_a1, Rat_b1), im_a1, d_a1)
            // add(Ext_a2, Rat_b2) = Ext(add(re_a2, Rat_b2), im_a2, d_a2)
            // d_a1 == d_a2 from same_radicand(a1,a2) ✓
            let rb1 = match b1 { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            let rb2 = match b2 { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            lemma_dts_add_preserves_same_radicand_both(
                *re_a1, *re_a2, DynTowerSpec::Rat(rb1), DynTowerSpec::Rat(rb2));
        },
        (DynTowerSpec::Ext(re_a1, im_a1, _), DynTowerSpec::Ext(re_a2, im_a2, _),
         DynTowerSpec::Ext(re_b1, im_b1, _), DynTowerSpec::Ext(re_b2, im_b2, _)) => {
            // add(Ext_a1, Ext_b1) = Ext(add(re_a1, re_b1), add(im_a1, im_b1), d_a1)
            // add(Ext_a2, Ext_b2) = Ext(add(re_a2, re_b2), add(im_a2, im_b2), d_a2)
            // d_a1 == d_a2 ✓
            lemma_dts_add_preserves_same_radicand_both(*re_a1, *re_a2, *re_b1, *re_b2);
            lemma_dts_add_preserves_same_radicand_both(*im_a1, *im_a2, *im_b1, *im_b2);
        },
        // All cross-depth cases: result is cross-depth → same_radicand = true
        _ => {},
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
    match (c, a, b) {
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {},
        (DynTowerSpec::Rat(rc), DynTowerSpec::Ext(re_a, im_a, _), DynTowerSpec::Ext(re_b, im_b, _)) => {
            // mul(Rat(rc), Ext_a) = Ext(mul(Rat(rc), re_a), mul(Rat(rc), im_a), d_a)
            // mul(Rat(rc), Ext_b) = Ext(mul(Rat(rc), re_b), mul(Rat(rc), im_b), d_b)
            lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, DynTowerSpec::Rat(rc));
            lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, DynTowerSpec::Rat(rc));
        },
        (DynTowerSpec::Rat(_), DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _)) => {},
        (DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _), DynTowerSpec::Rat(_)) => {},
        (DynTowerSpec::Ext(re_c, im_c, d_c), DynTowerSpec::Rat(_), DynTowerSpec::Rat(_)) => {
            let ra = match a { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            let rb = match b { DynTowerSpec::Rat(r) => r, _ => arbitrary() };
            lemma_dts_mul_preserves_same_radicand_right(
                DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *re_c);
            lemma_dts_mul_preserves_same_radicand_right(
                DynTowerSpec::Rat(ra), DynTowerSpec::Rat(rb), *im_c);
        },
        (DynTowerSpec::Ext(re_c, im_c, d_c), DynTowerSpec::Ext(re_a, im_a, _), DynTowerSpec::Ext(re_b, im_b, _)) => {
            // mul(Ext_c, Ext_a) = Ext(add(re_c*re_a, d_c*(im_c*im_a)), add(re_c*im_a, im_c*re_a), d_c)
            // mul(Ext_c, Ext_b) = Ext(add(re_c*re_b, d_c*(im_c*im_b)), add(re_c*im_b, im_c*re_b), d_c)
            // same d_c ✓. Need same_radicand for re and im sub-components.
            lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *re_c);
            lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *im_c);
            lemma_dts_mul_preserves_same_radicand_right(
                dts_mul(*im_c, *im_a), dts_mul(*im_c, *im_b), *d_c);
            // re: same_radicand(add(re_c*re_a, d_c*(im_c*im_a)), add(re_c*re_b, d_c*(im_c*im_b)))
            lemma_dts_add_preserves_same_radicand_both(
                dts_mul(*re_c, *re_a), dts_mul(*re_c, *re_b),
                dts_mul(*d_c, dts_mul(*im_c, *im_a)), dts_mul(*d_c, dts_mul(*im_c, *im_b)));
            // im: same_radicand(add(re_c*im_a, im_c*re_a), add(re_c*im_b, im_c*re_b))
            lemma_dts_mul_preserves_same_radicand_right(*im_a, *im_b, *re_c);
            lemma_dts_mul_preserves_same_radicand_right(*re_a, *re_b, *im_c);
            lemma_dts_add_preserves_same_radicand_both(
                dts_mul(*re_c, *im_a), dts_mul(*re_c, *im_b),
                dts_mul(*im_c, *re_a), dts_mul(*im_c, *re_b));
        },
        (DynTowerSpec::Ext(_, _, _), DynTowerSpec::Rat(_), DynTowerSpec::Ext(_, _, _)) => {},
        (DynTowerSpec::Ext(_, _, _), DynTowerSpec::Ext(_, _, _), DynTowerSpec::Rat(_)) => {},
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

} // verus!
