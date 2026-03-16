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

} // verus!
