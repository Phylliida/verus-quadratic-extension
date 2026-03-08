use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::field::Field;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::determinant;
use verus_algebra::inequalities;
use verus_algebra::inequalities::lemma_nonneg_add;
use verus_algebra::inequalities::lemma_square_mul;
use verus_algebra::inequalities::lemma_square_le_implies_le;
use verus_algebra::lemmas::partial_order_lemmas;
use crate::radicand::Radicand;
use crate::radicand::PositiveRadicand;
use crate::ordered::*;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Helper lemmas for ring/field proofs
// ═══════════════════════════════════════════════════════════════════
//
// These provide intermediate algebraic identities that simplify the
// main Ring and Field proofs. Each is a standalone lemma that can
// be verified independently, keeping rlimits manageable.

// ─── Small helpers ────────────────────────────────────────────────

/// a * (b * c) ≡ b * (a * c)   (swap first two factors)
pub proof fn lemma_mul_swap_first_two<F: Field>(a: F, b: F, c: F)
    ensures
        a.mul(b.mul(c)).eqv(b.mul(a.mul(c))),
{
    // a*(b*c) ≡ (a*b)*c      [assoc rev]
    F::axiom_mul_associative(a, b, c);
    F::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
    // (a*b)*c ≡ (b*a)*c      [comm on a,b + congruence]
    F::axiom_mul_commutative(a, b);
    F::axiom_mul_congruence_left(a.mul(b), b.mul(a), c);
    // (b*a)*c ≡ b*(a*c)      [assoc]
    F::axiom_mul_associative(b, a, c);
    // chain
    F::axiom_eqv_transitive(a.mul(b.mul(c)), a.mul(b).mul(c), b.mul(a).mul(c));
    F::axiom_eqv_transitive(a.mul(b.mul(c)), b.mul(a).mul(c), b.mul(a.mul(c)));
}

/// (a * b) * c ≡ (a * c) * b   (swap last two factors)
pub proof fn lemma_mul_swap_last_two<F: Field>(a: F, b: F, c: F)
    ensures
        a.mul(b).mul(c).eqv(a.mul(c).mul(b)),
{
    // (a*b)*c ≡ a*(b*c)      [assoc]
    F::axiom_mul_associative(a, b, c);
    // a*(b*c) ≡ a*(c*b)      [comm on b,c + congruence]
    F::axiom_mul_commutative(b, c);
    ring_lemmas::lemma_mul_congruence_right::<F>(a, b.mul(c), c.mul(b));
    // a*(c*b) ≡ (a*c)*b      [assoc rev]
    F::axiom_mul_associative(a, c, b);
    F::axiom_eqv_symmetric(a.mul(c).mul(b), a.mul(c.mul(b)));
    // chain
    F::axiom_eqv_transitive(a.mul(b).mul(c), a.mul(b.mul(c)), a.mul(c.mul(b)));
    F::axiom_eqv_transitive(a.mul(b).mul(c), a.mul(c.mul(b)), a.mul(c).mul(b));
}

/// a * (b * c) ≡ (a * b) * c  (assoc, LHS nested → LHS flat)
/// Just a convenience wrapper with the "useful" direction.
pub proof fn lemma_mul_assoc_rev<F: Field>(a: F, b: F, c: F)
    ensures
        a.mul(b.mul(c)).eqv(a.mul(b).mul(c)),
{
    F::axiom_mul_associative(a, b, c);
    F::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
}

// ═══════════════════════════════════════════════════════════════════
//  Multiplicative associativity: real part
// ═══════════════════════════════════════════════════════════════════
//
// LHS = (x * (y * z)).re
//     = x.re * (y.re*z.re + y.im*z.im*d) + x.im * (y.re*z.im + y.im*z.re) * d
//
// RHS = ((x * y) * z).re
//     = (x.re*y.re + x.im*y.im*d) * z.re + (x.re*y.im + x.im*y.re) * z.im * d
//
// Both expand to: x.re*y.re*z.re + x.re*y.im*z.im*d
//               + x.im*y.re*z.im*d + x.im*y.im*z.re*d
//
// The proof guides Z3 through distributivity and reassociation.

#[verifier::rlimit(40)]
pub proof fn lemma_mul_assoc_re<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
    z: SpecQuadExt<F, R>,
)
    ensures
        qe_mul::<F, R>(x, qe_mul::<F, R>(y, z)).re.eqv(
            qe_mul::<F, R>(qe_mul::<F, R>(x, y), z).re
        ),
{
    let a = x.re; let b = x.im;
    let c = y.re; let e = y.im;
    let f = z.re; let g = z.im;
    let d = R::value();

    // LHS real = a*(c*f + e*g*d) + b*(c*g + e*f)*d
    // Distribute a: a*(c*f) + a*(e*g*d)
    F::axiom_mul_distributes_left(a, c.mul(f), e.mul(g).mul(d));

    // Distribute b into (c*g + e*f): b*(c*g) + b*(e*f)
    F::axiom_mul_distributes_left(b, c.mul(g), e.mul(f));
    // Then multiply by d: (b*(c*g) + b*(e*f))*d = b*(c*g)*d + b*(e*f)*d
    ring_lemmas::lemma_mul_distributes_right::<F>(
        b.mul(c.mul(g)), b.mul(e.mul(f)), d,
    );
    // Congruence chain: b*(c*g + e*f)*d ≡ b*(c*g)*d + b*(e*f)*d
    F::axiom_mul_congruence_left(
        b.mul(c.mul(g).add(e.mul(f))),
        b.mul(c.mul(g)).add(b.mul(e.mul(f))),
        d,
    );
    F::axiom_eqv_transitive(
        b.mul(c.mul(g).add(e.mul(f))).mul(d),
        b.mul(c.mul(g)).add(b.mul(e.mul(f))).mul(d),
        b.mul(c.mul(g)).mul(d).add(b.mul(e.mul(f)).mul(d)),
    );

    // So LHS = a*(c*f) + a*(e*g*d) + b*(c*g)*d + b*(e*f)*d
    // Combine: [a*(c*f) + a*(e*g*d)] + [b*(c*g)*d + b*(e*f)*d]
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(f).add(e.mul(g).mul(d))),
        a.mul(c.mul(f)).add(a.mul(e.mul(g).mul(d))),
        b.mul(c.mul(g).add(e.mul(f))).mul(d),
        b.mul(c.mul(g)).mul(d).add(b.mul(e.mul(f)).mul(d)),
    );

    // LHS ≡ a*(c*f) + a*(e*g*d) + b*(c*g)*d + b*(e*f)*d
    // Use add_assoc to flatten: ((p + q) + r) + s ≡ ...
    // Actually, we have (p + q) + (r + s) which is already 4 terms grouped as 2+2

    // RHS real = (a*c + b*e*d)*f + (a*e + b*c)*g*d
    // Distribute f: a*c*f + b*e*d*f
    ring_lemmas::lemma_mul_distributes_right::<F>(a.mul(c), b.mul(e).mul(d), f);
    // Distribute g: a*e*g + b*c*g, then *d
    ring_lemmas::lemma_mul_distributes_right::<F>(a.mul(e), b.mul(c), g);
    // (a*e*g + b*c*g)*d = a*e*g*d + b*c*g*d
    ring_lemmas::lemma_mul_distributes_right::<F>(
        a.mul(e).mul(g), b.mul(c).mul(g), d,
    );
    F::axiom_mul_congruence_left(
        a.mul(e).add(b.mul(c)).mul(g),
        a.mul(e).mul(g).add(b.mul(c).mul(g)),
        d,
    );
    F::axiom_eqv_transitive(
        a.mul(e).add(b.mul(c)).mul(g).mul(d),
        a.mul(e).mul(g).add(b.mul(c).mul(g)).mul(d),
        a.mul(e).mul(g).mul(d).add(b.mul(c).mul(g).mul(d)),
    );

    // RHS ≡ a*c*f + b*e*d*f + a*e*g*d + b*c*g*d
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c).add(b.mul(e).mul(d)).mul(f),
        a.mul(c).mul(f).add(b.mul(e).mul(d).mul(f)),
        a.mul(e).add(b.mul(c)).mul(g).mul(d),
        a.mul(e).mul(g).mul(d).add(b.mul(c).mul(g).mul(d)),
    );

    // Now show term-by-term equality between the 4 LHS and 4 RHS terms:

    // Term 1: a*(c*f) ≡ a*c*f  (just assoc)
    lemma_mul_assoc_rev::<F>(a, c, f);

    // Term 2: a*(e*g*d) ≡ a*e*g*d  (assoc)
    lemma_mul_assoc_rev::<F>(a, e.mul(g), d);
    lemma_mul_assoc_rev::<F>(a, e, g);
    F::axiom_mul_congruence_left(a.mul(e.mul(g)), a.mul(e).mul(g), d);
    F::axiom_eqv_transitive(
        a.mul(e.mul(g).mul(d)),
        a.mul(e.mul(g)).mul(d),
        a.mul(e).mul(g).mul(d),
    );

    // Term 3: b*(c*g)*d ≡ b*c*g*d  (assoc)
    lemma_mul_assoc_rev::<F>(b, c, g);
    F::axiom_mul_congruence_left(b.mul(c.mul(g)), b.mul(c).mul(g), d);

    // Term 4: b*(e*f)*d ≡ b*e*d*f  (assoc + swap last two of b*e*f → b*e*d*f??)
    // b*(e*f)*d: we need this ≡ b*e*d*f = (b*e)*d*f
    // b*(e*f)*d ≡ b*(e*f*d) [assoc]
    //           ≡ b*(e*d*f) [swap last two in e*f*d]
    //           ≡ (b*e)*(d*f) [assoc]... actually let's just do it:
    // b*(e*f)*d ≡ (b*(e*f))*d [already flat]
    // b*(e*f) ≡ (b*e)*f [assoc rev]
    lemma_mul_assoc_rev::<F>(b, e, f);
    // so b*(e*f)*d ≡ (b*e)*f*d
    F::axiom_mul_congruence_left(b.mul(e.mul(f)), b.mul(e).mul(f), d);
    // (b*e)*f*d ≡ (b*e)*d*f [swap last two]
    lemma_mul_swap_last_two::<F>(b.mul(e), f, d);
    F::axiom_eqv_transitive(
        b.mul(e.mul(f)).mul(d),
        b.mul(e).mul(f).mul(d),
        b.mul(e).mul(d).mul(f),
    );

    // Now combine: LHS 4 terms ≡ RHS 4 terms
    // LHS (2+2): (a*(c*f) + a*(e*g*d)) + (b*(c*g)*d + b*(e*f)*d)
    // RHS (2+2): (a*c*f + b*e*d*f) + (a*e*g*d + b*c*g*d)

    // Group LHS as: term1 + term4 + term2 + term3
    // = a*c*f + b*e*d*f + a*e*g*d + b*c*g*d
    // which equals RHS.

    // We need to reorder the LHS sum. LHS is currently:
    //   (term1 + term2) + (term3 + term4)
    // RHS is:
    //   (term1 + term4) + (term2 + term3)
    // These are equal by add_comm and add_assoc, but let's guide Z3.

    // First, establish the 4-term congruences:
    // LHS_term1 ≡ RHS_term1: done (a*(c*f) ≡ a*c*f)
    // LHS_term2 ≡ RHS_term3: a*(e*g*d) ≡ a*e*g*d
    // LHS_term3 ≡ RHS_term4: b*(c*g)*d ≡ b*c*g*d
    // LHS_term4 ≡ RHS_term2: b*(e*f)*d ≡ b*e*d*f

    // Rewrite LHS as congruent 4-terms:
    // (a*(c*f) + a*(e*g*d)) + (b*(c*g)*d + b*(e*f)*d)
    // ≡ (a*c*f + a*e*g*d) + (b*c*g*d + b*e*d*f)

    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(f)), a.mul(c).mul(f),
        a.mul(e.mul(g).mul(d)), a.mul(e).mul(g).mul(d),
    );
    additive_group_lemmas::lemma_add_congruence::<F>(
        b.mul(c.mul(g)).mul(d), b.mul(c).mul(g).mul(d),
        b.mul(e.mul(f)).mul(d), b.mul(e).mul(d).mul(f),
    );
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(f)).add(a.mul(e.mul(g).mul(d))),
        a.mul(c).mul(f).add(a.mul(e).mul(g).mul(d)),
        b.mul(c.mul(g)).mul(d).add(b.mul(e.mul(f)).mul(d)),
        b.mul(c).mul(g).mul(d).add(b.mul(e).mul(d).mul(f)),
    );

    // Now rearrange: (P + Q) + (R + S) ≡ (P + S) + (Q + R)
    // where P = a*c*f, Q = a*e*g*d, R = b*c*g*d, S = b*e*d*f
    lemma_add_swap_inner::<F>(
        a.mul(c).mul(f),
        a.mul(e).mul(g).mul(d),
        b.mul(c).mul(g).mul(d),
        b.mul(e).mul(d).mul(f),
    );

    // Chain everything together: LHS.re ≡ ... ≡ RHS.re
    // LHS.re = a*(cf + egd) + b*(cg + ef)*d
    //        ≡ (a*cf + a*egd) + (b*cg*d + b*ef*d)          [distribute]
    //        ≡ (acf + aegd) + (bcgd + bedf)                 [reassociate terms]
    //        ≡ (acf + bedf) + (aegd + bcgd)                 [swap inner]
    //        = RHS.re = (ac + bed)*f + (ae + bc)*g*d
    //                 ≡ (acf + bedf) + (aegd + bcgd)        [distribute]
    let lhs_re = qe_mul::<F, R>(x, qe_mul::<F, R>(y, z)).re;
    let rhs_re = qe_mul::<F, R>(qe_mul::<F, R>(x, y), z).re;

    // LHS.re ≡ (a*cf + a*egd) + (b*cg*d + b*ef*d)
    let lhs_expanded = a.mul(c.mul(f)).add(a.mul(e.mul(g).mul(d)))
        .add(b.mul(c.mul(g)).mul(d).add(b.mul(e.mul(f)).mul(d)));

    // After term reassoc: (acf + aegd) + (bcgd + bedf)
    let lhs_reassoc = a.mul(c).mul(f).add(a.mul(e).mul(g).mul(d))
        .add(b.mul(c).mul(g).mul(d).add(b.mul(e).mul(d).mul(f)));

    // After swap: (acf + bedf) + (aegd + bcgd)
    let lhs_swapped = a.mul(c).mul(f).add(b.mul(e).mul(d).mul(f))
        .add(a.mul(e).mul(g).mul(d).add(b.mul(c).mul(g).mul(d)));

    // RHS.re ≡ (acf + bedf) + (aegd + bcgd)
    let rhs_expanded = a.mul(c).mul(f).add(b.mul(e).mul(d).mul(f))
        .add(a.mul(e).mul(g).mul(d).add(b.mul(c).mul(g).mul(d)));

    // lhs_swapped == rhs_expanded structurally, so Z3 sees they're equal.
    // Now chain: lhs_re ≡ lhs_expanded ≡ lhs_reassoc ≡ lhs_swapped = rhs_expanded ≡ rhs_re
    F::axiom_eqv_transitive(lhs_expanded, lhs_reassoc, lhs_swapped);

    // lhs_re ≡ lhs_expanded (from the distribute step above)
    // We established this via the add_congruence calls; need to assert the chain.
    // The distribute congruences gave us lhs_re ≡ lhs_expanded
    // (via the two add_congruence calls at the top)

    F::axiom_eqv_transitive(lhs_re, lhs_expanded, lhs_swapped);

    // rhs_re ≡ rhs_expanded (from the distribute step)
    F::axiom_eqv_symmetric(rhs_re, rhs_expanded);

    // lhs_swapped == rhs_expanded (structural), so:
    F::axiom_eqv_reflexive(lhs_swapped);
    F::axiom_eqv_transitive(lhs_re, lhs_swapped, rhs_expanded);

    // rhs_expanded ≡ rhs_re
    F::axiom_eqv_transitive(lhs_re, rhs_expanded, rhs_re);
}

/// (P + Q) + (R + S) ≡ (P + S) + (Q + R)
///
/// Rearranges the inner pair of a 4-element sum.
pub proof fn lemma_add_swap_inner<F: Field>(p: F, q: F, r: F, s: F)
    ensures
        p.add(q).add(r.add(s)).eqv(p.add(s).add(q.add(r))),
{
    // Step 1: assoc to get P + (Q + (R + S))
    F::axiom_add_associative(p, q, r.add(s));

    // Step 2: inner assoc: Q + (R + S) ≡ (Q + R) + S
    F::axiom_add_associative(q, r, s);
    F::axiom_eqv_symmetric(q.add(r).add(s), q.add(r.add(s)));

    // Step 3: P + (Q + (R + S)) ≡ P + ((Q + R) + S)
    F::axiom_eqv_reflexive(p);
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(p, q.add(r.add(s)), q.add(r).add(s));
    F::axiom_eqv_transitive(
        p.add(q).add(r.add(s)),
        p.add(q.add(r.add(s))),
        p.add(q.add(r).add(s)),
    );

    // Step 4: comm inner: (Q + R) + S ≡ S + (Q + R)
    F::axiom_add_commutative(q.add(r), s);

    // Step 5: P + ((Q + R) + S) ≡ P + (S + (Q + R))
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(p, q.add(r).add(s), s.add(q.add(r)));
    F::axiom_eqv_transitive(
        p.add(q).add(r.add(s)),
        p.add(q.add(r).add(s)),
        p.add(s.add(q.add(r))),
    );

    // Step 6: assoc rev: P + (S + (Q + R)) ≡ (P + S) + (Q + R)
    F::axiom_add_associative(p, s, q.add(r));
    F::axiom_eqv_symmetric(p.add(s).add(q.add(r)), p.add(s.add(q.add(r))));
    F::axiom_eqv_transitive(
        p.add(q).add(r.add(s)),
        p.add(s.add(q.add(r))),
        p.add(s).add(q.add(r)),
    );
}


// ═══════════════════════════════════════════════════════════════════
//  Multiplicative associativity: imaginary part
// ═══════════════════════════════════════════════════════════════════
//
// LHS = (x * (y * z)).im
//     = x.re * (y.re*z.im + y.im*z.re) + x.im * (y.re*z.re + y.im*z.im*d)
//
// RHS = ((x * y) * z).im
//     = (x.re*y.re + x.im*y.im*d) * z.im + (x.re*y.im + x.im*y.re) * z.re
//
// Both expand to: x.re*y.re*z.im + x.re*y.im*z.re
//               + x.im*y.re*z.re + x.im*y.im*z.im*d

#[verifier::rlimit(40)]
pub proof fn lemma_mul_assoc_im<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
    z: SpecQuadExt<F, R>,
)
    ensures
        qe_mul::<F, R>(x, qe_mul::<F, R>(y, z)).im.eqv(
            qe_mul::<F, R>(qe_mul::<F, R>(x, y), z).im
        ),
{
    let a = x.re; let b = x.im;
    let c = y.re; let e = y.im;
    let f = z.re; let g = z.im;
    let d = R::value();

    // LHS.im = a*(c*g + e*f) + b*(c*f + e*g*d)
    // Distribute a: a*(c*g) + a*(e*f)
    F::axiom_mul_distributes_left(a, c.mul(g), e.mul(f));
    // Distribute b: b*(c*f) + b*(e*g*d)
    F::axiom_mul_distributes_left(b, c.mul(f), e.mul(g).mul(d));

    // LHS.im ≡ (a*cg + a*ef) + (b*cf + b*egd)
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(g).add(e.mul(f))),
        a.mul(c.mul(g)).add(a.mul(e.mul(f))),
        b.mul(c.mul(f).add(e.mul(g).mul(d))),
        b.mul(c.mul(f)).add(b.mul(e.mul(g).mul(d))),
    );

    // Reassociate each term:
    // a*(c*g) ≡ a*c*g
    lemma_mul_assoc_rev::<F>(a, c, g);
    // a*(e*f) ≡ a*e*f
    lemma_mul_assoc_rev::<F>(a, e, f);
    // b*(c*f) ≡ b*c*f
    lemma_mul_assoc_rev::<F>(b, c, f);
    // b*(e*g*d) ≡ b*e*g*d
    lemma_mul_assoc_rev::<F>(b, e.mul(g), d);
    lemma_mul_assoc_rev::<F>(b, e, g);
    F::axiom_mul_congruence_left(b.mul(e.mul(g)), b.mul(e).mul(g), d);
    F::axiom_eqv_transitive(
        b.mul(e.mul(g).mul(d)),
        b.mul(e.mul(g)).mul(d),
        b.mul(e).mul(g).mul(d),
    );

    // LHS reassociated: (acg + aef) + (bcf + begd)
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(g)), a.mul(c).mul(g),
        a.mul(e.mul(f)), a.mul(e).mul(f),
    );
    additive_group_lemmas::lemma_add_congruence::<F>(
        b.mul(c.mul(f)), b.mul(c).mul(f),
        b.mul(e.mul(g).mul(d)), b.mul(e).mul(g).mul(d),
    );
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c.mul(g)).add(a.mul(e.mul(f))),
        a.mul(c).mul(g).add(a.mul(e).mul(f)),
        b.mul(c.mul(f)).add(b.mul(e.mul(g).mul(d))),
        b.mul(c).mul(f).add(b.mul(e).mul(g).mul(d)),
    );

    // RHS.im = (ac + bed)*g + (ae + bc)*f
    // Distribute g: a*c*g + b*e*d*g
    ring_lemmas::lemma_mul_distributes_right::<F>(a.mul(c), b.mul(e).mul(d), g);
    // Distribute f: a*e*f + b*c*f
    ring_lemmas::lemma_mul_distributes_right::<F>(a.mul(e), b.mul(c), f);

    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c).add(b.mul(e).mul(d)).mul(g),
        a.mul(c).mul(g).add(b.mul(e).mul(d).mul(g)),
        a.mul(e).add(b.mul(c)).mul(f),
        a.mul(e).mul(f).add(b.mul(c).mul(f)),
    );

    // RHS expanded: (acg + bedg) + (aef + bcf)
    // LHS expanded: (acg + aef) + (bcf + begd)
    // Need: bedg ≡ begd (swap last two: d,g)
    lemma_mul_swap_last_two::<F>(b.mul(e), d, g);

    // Then reorder: (acg + aef) + (bcf + begd)
    //             ≡ (acg + begd) + (aef + bcf)   [swap inner]
    //             ≡ (acg + bedg) + (aef + bcf)   [bedg ≡ begd → begd ≡ bedg]
    //             = RHS
    F::axiom_eqv_symmetric(b.mul(e).mul(d).mul(g), b.mul(e).mul(g).mul(d));

    // Swap inner in LHS: (acg + aef) + (bcf + begd)
    //                   ≡ (acg + begd) + (aef + bcf)
    lemma_add_swap_inner::<F>(
        a.mul(c).mul(g),
        a.mul(e).mul(f),
        b.mul(c).mul(f),
        b.mul(e).mul(g).mul(d),
    );

    // begd ≡ bedg in the first group
    F::axiom_eqv_reflexive(a.mul(c).mul(g));
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(
        a.mul(c).mul(g),
        b.mul(e).mul(g).mul(d),
        b.mul(e).mul(d).mul(g),
    );
    F::axiom_eqv_reflexive(a.mul(e).mul(f).add(b.mul(c).mul(f)));
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(c).mul(g).add(b.mul(e).mul(g).mul(d)),
        a.mul(c).mul(g).add(b.mul(e).mul(d).mul(g)),
        a.mul(e).mul(f).add(b.mul(c).mul(f)),
        a.mul(e).mul(f).add(b.mul(c).mul(f)),
    );

    // Chain LHS all the way to RHS
    let lhs_im = qe_mul::<F, R>(x, qe_mul::<F, R>(y, z)).im;
    let rhs_im = qe_mul::<F, R>(qe_mul::<F, R>(x, y), z).im;
    let lhs_dist = a.mul(c.mul(g)).add(a.mul(e.mul(f)))
        .add(b.mul(c.mul(f)).add(b.mul(e.mul(g).mul(d))));
    let lhs_reassoc = a.mul(c).mul(g).add(a.mul(e).mul(f))
        .add(b.mul(c).mul(f).add(b.mul(e).mul(g).mul(d)));
    let lhs_swapped = a.mul(c).mul(g).add(b.mul(e).mul(g).mul(d))
        .add(a.mul(e).mul(f).add(b.mul(c).mul(f)));
    let lhs_final = a.mul(c).mul(g).add(b.mul(e).mul(d).mul(g))
        .add(a.mul(e).mul(f).add(b.mul(c).mul(f)));
    let rhs_dist = a.mul(c).mul(g).add(b.mul(e).mul(d).mul(g))
        .add(a.mul(e).mul(f).add(b.mul(c).mul(f)));

    // lhs_final == rhs_dist structurally
    F::axiom_eqv_reflexive(lhs_final);

    // Chain: lhs_im ≡ lhs_dist ≡ lhs_reassoc ≡ lhs_swapped ≡ lhs_final = rhs_dist ≡ rhs_im
    F::axiom_eqv_transitive(lhs_im, lhs_dist, lhs_reassoc);
    F::axiom_eqv_transitive(lhs_im, lhs_reassoc, lhs_swapped);
    F::axiom_eqv_transitive(lhs_im, lhs_swapped, lhs_final);

    // rhs_im ≡ rhs_dist
    F::axiom_eqv_symmetric(rhs_im, rhs_dist);

    F::axiom_eqv_transitive(lhs_im, lhs_final, rhs_dist);
    F::axiom_eqv_transitive(lhs_im, rhs_dist, rhs_im);
}


// ═══════════════════════════════════════════════════════════════════
//  Left distributivity: real and imaginary parts
// ═══════════════════════════════════════════════════════════════════

/// Real part of x*(y+z) ≡ real part of x*y + x*z
pub proof fn lemma_mul_distributes_left_re<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
    z: SpecQuadExt<F, R>,
)
    ensures
        qe_mul::<F, R>(x, qe_add::<F, R>(y, z)).re.eqv(
            qe_add::<F, R>(qe_mul::<F, R>(x, y), qe_mul::<F, R>(x, z)).re
        ),
{
    let a = x.re; let b = x.im;
    let d = R::value();

    // LHS.re = a*(y.re+z.re) + b*(y.im+z.im)*d
    // RHS.re = (a*y.re + b*y.im*d) + (a*z.re + b*z.im*d)

    // Distribute a:
    F::axiom_mul_distributes_left(a, y.re, z.re);
    // Distribute b:
    F::axiom_mul_distributes_left(b, y.im, z.im);
    // b*(y.im+z.im)*d ≡ (b*y.im + b*z.im)*d ≡ b*y.im*d + b*z.im*d
    F::axiom_mul_congruence_left(
        b.mul(y.im.add(z.im)),
        b.mul(y.im).add(b.mul(z.im)),
        d,
    );
    ring_lemmas::lemma_mul_distributes_right::<F>(b.mul(y.im), b.mul(z.im), d);
    F::axiom_eqv_transitive(
        b.mul(y.im.add(z.im)).mul(d),
        b.mul(y.im).add(b.mul(z.im)).mul(d),
        b.mul(y.im).mul(d).add(b.mul(z.im).mul(d)),
    );

    // LHS.re ≡ (a*y.re + a*z.re) + (b*y.im*d + b*z.im*d)
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(y.re.add(z.re)),
        a.mul(y.re).add(a.mul(z.re)),
        b.mul(y.im.add(z.im)).mul(d),
        b.mul(y.im).mul(d).add(b.mul(z.im).mul(d)),
    );

    // Rearrange: (P + Q) + (R + S) ≡ (P + R) + (Q + S)
    // where P=a*y.re, Q=a*z.re, R=b*y.im*d, S=b*z.im*d
    // swap_inner gives (P+Q)+(R+S) ≡ (P+S)+(Q+R), so we first comm R,S:
    // (P+Q)+(R+S) ≡ (P+Q)+(S+R) [comm on R+S]
    F::axiom_add_commutative(b.mul(y.im).mul(d), b.mul(z.im).mul(d));
    F::axiom_eqv_reflexive(a.mul(y.re).add(a.mul(z.re)));
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(y.re).add(a.mul(z.re)),
        a.mul(y.re).add(a.mul(z.re)),
        b.mul(y.im).mul(d).add(b.mul(z.im).mul(d)),
        b.mul(z.im).mul(d).add(b.mul(y.im).mul(d)),
    );
    // Now swap_inner(P, Q, S, R): (P+Q)+(S+R) ≡ (P+R)+(Q+S)
    lemma_add_swap_inner::<F>(
        a.mul(y.re), a.mul(z.re), b.mul(z.im).mul(d), b.mul(y.im).mul(d),
    );
    // Chain: LHS.re ≡ (P+Q)+(R+S) ≡ (P+Q)+(S+R) ≡ (P+R)+(Q+S) = RHS.re
    let lhs_re = qe_mul::<F, R>(x, qe_add::<F, R>(y, z)).re;
    let expanded = a.mul(y.re).add(a.mul(z.re)).add(b.mul(y.im).mul(d).add(b.mul(z.im).mul(d)));
    let commuted = a.mul(y.re).add(a.mul(z.re)).add(b.mul(z.im).mul(d).add(b.mul(y.im).mul(d)));
    let target = a.mul(y.re).add(b.mul(y.im).mul(d)).add(a.mul(z.re).add(b.mul(z.im).mul(d)));
    F::axiom_eqv_transitive(lhs_re, expanded, commuted);
    F::axiom_eqv_transitive(lhs_re, commuted, target);
}

/// Imaginary part of x*(y+z) ≡ imaginary part of x*y + x*z
pub proof fn lemma_mul_distributes_left_im<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
    z: SpecQuadExt<F, R>,
)
    ensures
        qe_mul::<F, R>(x, qe_add::<F, R>(y, z)).im.eqv(
            qe_add::<F, R>(qe_mul::<F, R>(x, y), qe_mul::<F, R>(x, z)).im
        ),
{
    let a = x.re; let b = x.im;

    // LHS.im = a*(y.im+z.im) + b*(y.re+z.re)
    // RHS.im = (a*y.im + b*y.re) + (a*z.im + b*z.re)

    F::axiom_mul_distributes_left(a, y.im, z.im);
    F::axiom_mul_distributes_left(b, y.re, z.re);
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(y.im.add(z.im)),
        a.mul(y.im).add(a.mul(z.im)),
        b.mul(y.re.add(z.re)),
        b.mul(y.re).add(b.mul(z.re)),
    );

    // (P+Q)+(R+S) → (P+R)+(Q+S) via comm on R,S then swap_inner(P,Q,S,R)
    // P=a*y.im, Q=a*z.im, R=b*y.re, S=b*z.re
    F::axiom_add_commutative(b.mul(y.re), b.mul(z.re));
    F::axiom_eqv_reflexive(a.mul(y.im).add(a.mul(z.im)));
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(y.im).add(a.mul(z.im)),
        a.mul(y.im).add(a.mul(z.im)),
        b.mul(y.re).add(b.mul(z.re)),
        b.mul(z.re).add(b.mul(y.re)),
    );
    lemma_add_swap_inner::<F>(
        a.mul(y.im), a.mul(z.im), b.mul(z.re), b.mul(y.re),
    );
    let lhs_im = qe_mul::<F, R>(x, qe_add::<F, R>(y, z)).im;
    let expanded = a.mul(y.im).add(a.mul(z.im)).add(b.mul(y.re).add(b.mul(z.re)));
    let commuted = a.mul(y.im).add(a.mul(z.im)).add(b.mul(z.re).add(b.mul(y.re)));
    let target = a.mul(y.im).add(b.mul(y.re)).add(a.mul(z.im).add(b.mul(z.re)));
    F::axiom_eqv_transitive(lhs_im, expanded, commuted);
    F::axiom_eqv_transitive(lhs_im, commuted, target);
}


// ═══════════════════════════════════════════════════════════════════
//  Norm is nonzero for nonzero elements (requires non-square radicand)
// ═══════════════════════════════════════════════════════════════════

/// If x ≢ 0 in the extension, then norm(x) ≢ 0 in F.
///
/// Proof by contradiction:
/// - If norm = 0 then a² ≡ b²d.
/// - Case b ≡ 0: then a² ≡ 0, so a ≡ 0, contradicting x ≢ 0.
/// - Case b ≢ 0: then (a/b)² ≡ d, contradicting non-squareness of d.
#[verifier::rlimit(30)]
pub proof fn lemma_norm_nonzero<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        !qe_eqv::<F, R>(x, qe_zero::<F, R>()),
    ensures
        !qe_norm::<F, R>(x).eqv(F::zero()),
{
    let d = R::value();
    let n = qe_norm::<F, R>(x);

    // Suppose norm ≡ 0 for contradiction
    if n.eqv(F::zero()) {
        // norm = a² - b²d ≡ 0 means a² ≡ b²d
        // i.e. a*a - b*b*d ≡ 0 → a*a ≡ b*b*d
        // (from sub ≡ 0 → lhs ≡ rhs)
        lemma_sub_eqv_zero_implies_eqv::<F>(x.re.mul(x.re), x.im.mul(x.im).mul(d));

        if x.im.eqv(F::zero()) {
            // b ≡ 0 → b² ≡ 0 → b²d ≡ 0 → a² ≡ 0 → a ≡ 0
            ring_lemmas::lemma_mul_congruence::<F>(x.im, F::zero(), x.im, F::zero());
            F::axiom_mul_zero_right(F::zero());
            F::axiom_eqv_transitive(x.im.mul(x.im), F::zero().mul(F::zero()), F::zero());
            F::axiom_mul_congruence_left(x.im.mul(x.im), F::zero(), d);
            ring_lemmas::lemma_mul_zero_left::<F>(d);
            F::axiom_eqv_transitive(x.im.mul(x.im).mul(d), F::zero().mul(d), F::zero());
            // a² ≡ b²d ≡ 0
            F::axiom_eqv_transitive(x.re.mul(x.re), x.im.mul(x.im).mul(d), F::zero());
            // a² ≡ 0 → a ≡ 0
            lemma_square_zero::<F>(x.re);
            // But then x = (0, 0) = zero, contradiction
            // x.re ≡ 0 and x.im ≡ 0 means qe_eqv(x, qe_zero) = true
            assert(qe_eqv::<F, R>(x, qe_zero::<F, R>()));
        } else {
            // b ≢ 0, so b has a reciprocal
            // Let q = a * b⁻¹. Show q² ≡ d.
            let b_inv = x.im.recip();

            // q = a * b⁻¹
            let q = x.re.mul(b_inv);

            // q² = (a*b⁻¹)*(a*b⁻¹) = a²*b⁻²
            // a² ≡ b²d
            // a²*b⁻² ≡ b²d*b⁻²
            ring_lemmas::lemma_mul_congruence_right::<F>(
                b_inv.mul(b_inv),
                x.re.mul(x.re),
                x.im.mul(x.im).mul(d),
            );
            // q*q = a*b⁻¹*a*b⁻¹
            //     ≡ a*a*b⁻¹*b⁻¹   (rearrange)
            //     ≡ a²*b⁻²
            //     ≡ b²d*b⁻²
            //     ≡ d*(b²*b⁻²)     (assoc+comm)
            //     ≡ d*(b*b⁻¹)*(b*b⁻¹)... hmm this needs care.

            // Actually: b²·d·b⁻² = (b·b⁻¹)·(b·b⁻¹)·d = 1·1·d = d
            // But we need to show this step by step.

            // b*b⁻¹ ≡ 1
            F::axiom_mul_recip_right(x.im);

            // b²*b⁻² = (b*b)*(b⁻¹*b⁻¹)
            // = b*(b*(b⁻¹*b⁻¹))    [assoc]
            // = b*((b*b⁻¹)*b⁻¹)    [assoc]
            // = b*(1*b⁻¹)           [b*b⁻¹ ≡ 1]
            // = b*b⁻¹               [1*x ≡ x]
            // = 1

            // b*b*recip(b)*recip(b)  →  1 step by step:
            // We need (b*b)*(recip(b)*recip(b)) ≡ 1
            // Use recip_mul: recip(b*b) ≡ recip(b)*recip(b)
            field_lemmas::lemma_recip_mul::<F>(x.im, x.im);
            // So (b*b)*recip(b*b) ≡ 1 (axiom, since b*b ≢ 0)
            field_lemmas::lemma_nonzero_product::<F>(x.im, x.im);
            F::axiom_mul_recip_right(x.im.mul(x.im));
            // (b*b)*(recip(b)*recip(b)) ≡ (b*b)*recip(b*b)
            // recip_mul gives recip(b*b).eqv(recip(b)*recip(b)), need symmetric
            F::axiom_eqv_symmetric(
                x.im.mul(x.im).recip(),
                x.im.recip().mul(x.im.recip()),
            );
            ring_lemmas::lemma_mul_congruence_right::<F>(
                x.im.mul(x.im),
                x.im.recip().mul(x.im.recip()),
                x.im.mul(x.im).recip(),
            );
            F::axiom_eqv_symmetric(
                x.im.mul(x.im).mul(x.im.recip().mul(x.im.recip())),
                x.im.mul(x.im).mul(x.im.mul(x.im).recip()),
            );
            // (b*b)*(recip(b)*recip(b)) ≡ 1
            F::axiom_eqv_transitive(
                x.im.mul(x.im).mul(x.im.recip().mul(x.im.recip())),
                x.im.mul(x.im).mul(x.im.mul(x.im).recip()),
                F::one(),
            );

            // Now: (b²d)*(b⁻²) ≡ d*(b²*b⁻²) ≡ d*1 ≡ d
            // (b²*d)*(b⁻²) = b²*(d*b⁻²) [assoc]
            //              = b²*(b⁻²*d) [comm]
            //              = (b²*b⁻²)*d [assoc rev]
            //              ≡ 1*d ≡ d
            let bb = x.im.mul(x.im);
            let bb_inv = x.im.recip().mul(x.im.recip());

            F::axiom_mul_associative(bb, d, bb_inv);
            F::axiom_mul_commutative(d, bb_inv);
            ring_lemmas::lemma_mul_congruence_right::<F>(bb, d.mul(bb_inv), bb_inv.mul(d));
            F::axiom_eqv_transitive(
                bb.mul(d).mul(bb_inv),
                bb.mul(d.mul(bb_inv)),
                bb.mul(bb_inv.mul(d)),
            );
            F::axiom_mul_associative(bb, bb_inv, d);
            F::axiom_eqv_symmetric(bb.mul(bb_inv).mul(d), bb.mul(bb_inv.mul(d)));
            F::axiom_eqv_transitive(
                bb.mul(d).mul(bb_inv),
                bb.mul(bb_inv.mul(d)),
                bb.mul(bb_inv).mul(d),
            );
            // bb*bb_inv ≡ 1 (proved above)
            F::axiom_mul_congruence_left(bb.mul(bb_inv), F::one(), d);
            F::axiom_eqv_transitive(
                bb.mul(d).mul(bb_inv),
                bb.mul(bb_inv).mul(d),
                F::one().mul(d),
            );
            ring_lemmas::lemma_mul_one_left::<F>(d);
            F::axiom_eqv_transitive(
                bb.mul(d).mul(bb_inv),
                F::one().mul(d),
                d,
            );

            // Now: q*q ≡ a*a*(b⁻¹*b⁻¹)
            // We need to show q*q = (a*b⁻¹)*(a*b⁻¹) ≡ (a*a)*(b⁻¹*b⁻¹)
            // (a*b⁻¹)*(a*b⁻¹) [assoc → a*(b⁻¹*(a*b⁻¹))]
            // a*(b⁻¹*a*b⁻¹) [swap first two in inner: b⁻¹*a ≡ a*b⁻¹]
            // Actually let's just use the lemma pattern:
            F::axiom_mul_associative(q, x.re, b_inv);
            // q*(a*b⁻¹) ≡ (q*a)*b⁻¹ reversed
            F::axiom_eqv_symmetric(q.mul(x.re).mul(b_inv), q.mul(x.re.mul(b_inv)));
            // q = a*b⁻¹, so q*a = a*b⁻¹*a
            // a*b⁻¹*a ≡ a*a*b⁻¹ [swap last two]
            lemma_mul_swap_last_two::<F>(x.re, b_inv, x.re);
            // (a*b⁻¹*a)*b⁻¹ = (a*a*b⁻¹)*b⁻¹ ≡ a*a*(b⁻¹*b⁻¹) [assoc]
            F::axiom_mul_congruence_left(
                x.re.mul(b_inv).mul(x.re),
                x.re.mul(x.re).mul(b_inv),
                b_inv,
            );
            F::axiom_mul_associative(x.re.mul(x.re), b_inv, b_inv);
            F::axiom_eqv_transitive(
                x.re.mul(b_inv).mul(x.re).mul(b_inv),
                x.re.mul(x.re).mul(b_inv).mul(b_inv),
                x.re.mul(x.re).mul(b_inv.mul(b_inv)),
            );

            // q*q ≡ (a*b⁻¹*a)*b⁻¹ ≡ a²*b⁻²
            F::axiom_eqv_transitive(
                q.mul(q),
                x.re.mul(b_inv).mul(x.re).mul(b_inv),
                x.re.mul(x.re).mul(b_inv.mul(b_inv)),
            );

            // a²*b⁻² ≡ (b²d)*b⁻² (from a² ≡ b²d, congruence)
            // mul_congruence_right gave bb_inv*a² ≡ bb_inv*b²d, need comm both sides
            F::axiom_mul_commutative(x.re.mul(x.re), bb_inv);
            F::axiom_mul_commutative(bb_inv, bb.mul(d));
            F::axiom_eqv_transitive(
                x.re.mul(x.re).mul(bb_inv),
                bb_inv.mul(x.re.mul(x.re)),
                bb_inv.mul(bb.mul(d)),
            );
            F::axiom_eqv_transitive(
                x.re.mul(x.re).mul(bb_inv),
                bb_inv.mul(bb.mul(d)),
                bb.mul(d).mul(bb_inv),
            );

            // a²*b⁻² ≡ b²d*b⁻² ≡ d
            F::axiom_eqv_transitive(
                x.re.mul(x.re).mul(bb_inv),
                bb.mul(d).mul(bb_inv),
                d,
            );

            // q*q ≡ a²*b⁻² ≡ d
            F::axiom_eqv_transitive(
                q.mul(q),
                x.re.mul(x.re).mul(bb_inv),
                d,
            );

            // But R::axiom_non_square says forall x, !x.mul(x).eqv(d)
            R::axiom_non_square(q);
            // Contradiction: q*q ≡ d but !q*q.eqv(d)
            assert(false);
        }
    }
}


// ═══════════════════════════════════════════════════════════════════
//  mul_recip_right: real and imaginary parts
// ═══════════════════════════════════════════════════════════════════

/// Real part of x * recip(x) ≡ 1
#[verifier::rlimit(40)]
pub proof fn lemma_mul_recip_right_re<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        !qe_eqv::<F, R>(x, qe_zero::<F, R>()),
        !qe_norm::<F, R>(x).eqv(F::zero()),
    ensures
        qe_mul::<F, R>(x, qe_recip::<F, R>(x)).re.eqv(F::one()),
{
    let a = x.re; let b = x.im;
    let d = R::value();
    let n = qe_norm::<F, R>(x);    // a² - b²d
    let n_inv = n.recip();

    // x * recip(x) real part:
    //   a*(a*n⁻¹) + b*((-b)*n⁻¹)*d
    // = a²*n⁻¹ + (-b²)*n⁻¹*d
    // = a²*n⁻¹ - b²*d*n⁻¹
    // = (a² - b²d)*n⁻¹
    // = n*n⁻¹ = 1

    // a*(a*n⁻¹) ≡ a²*n⁻¹ [assoc]
    lemma_mul_assoc_rev::<F>(a, a, n_inv);

    // b*((-b)*n⁻¹)*d:
    // b*((-b)*n⁻¹) [assoc rev] = (b*(-b))*n⁻¹
    lemma_mul_assoc_rev::<F>(b, b.neg(), n_inv);
    // b*(-b) ≡ -(b*b)
    ring_lemmas::lemma_mul_neg_right::<F>(b, b);
    F::axiom_mul_congruence_left(b.mul(b.neg()), b.mul(b).neg(), n_inv);
    F::axiom_eqv_transitive(
        b.mul(b.neg().mul(n_inv)),
        b.mul(b.neg()).mul(n_inv),
        b.mul(b).neg().mul(n_inv),
    );
    // (-(b²))*n⁻¹*d [swap last two] = (-(b²))*d*n⁻¹ ... actually let's
    // factor differently.

    // We want: a²*n⁻¹ + (-(b²))*n⁻¹*d ≡ (a² - b²d)*n⁻¹
    // = (a² + (-(b²d)))*n⁻¹
    // = (a² - b²d)*n⁻¹ = n*n⁻¹

    // (-(b²))*n⁻¹*d ≡ (-(b²))*d*n⁻¹ [swap last two]
    lemma_mul_swap_last_two::<F>(b.mul(b).neg(), n_inv, d);

    // (-(b²))*d ≡ -(b²*d) [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<F>(b.mul(b), d);

    // (-(b²))*d*n⁻¹ ≡ -(b²d)*n⁻¹
    F::axiom_mul_congruence_left(b.mul(b).neg().mul(d), b.mul(b).mul(d).neg(), n_inv);

    // b*((-b)*n⁻¹)*d ≡ (-(b²))*n⁻¹*d  [congruence with d]
    F::axiom_mul_congruence_left(b.mul(b.neg().mul(n_inv)), b.mul(b).neg().mul(n_inv), d);
    // Chain: b*((-b)*n⁻¹)*d ≡ (-(b²))*n⁻¹*d ≡ (-(b²))*d*n⁻¹ ≡ -(b²d)*n⁻¹
    F::axiom_eqv_transitive(
        b.mul(b.neg().mul(n_inv)).mul(d),
        b.mul(b).neg().mul(n_inv).mul(d),
        b.mul(b).neg().mul(d).mul(n_inv),
    );
    F::axiom_eqv_transitive(
        b.mul(b.neg().mul(n_inv)).mul(d),
        b.mul(b).neg().mul(d).mul(n_inv),
        b.mul(b).mul(d).neg().mul(n_inv),
    );

    // a²*n⁻¹ + -(b²d)*n⁻¹ ≡ (a² - b²d)*n⁻¹
    // = (a² + -(b²d))*n⁻¹ [sub is add neg]
    // Use right-distrib reversed: p*c + q*c ≡ (p+q)*c
    // i.e., a²*n⁻¹ + (-(b²d))*n⁻¹ ≡ (a² + -(b²d))*n⁻¹
    ring_lemmas::lemma_mul_distributes_right::<F>(
        a.mul(a), b.mul(b).mul(d).neg(), n_inv,
    );
    F::axiom_eqv_symmetric(
        a.mul(a).add(b.mul(b).mul(d).neg()).mul(n_inv),
        a.mul(a).mul(n_inv).add(b.mul(b).mul(d).neg().mul(n_inv)),
    );

    // Combine LHS ≡ a²*n⁻¹ + -(b²d)*n⁻¹
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(a.mul(n_inv)),
        a.mul(a).mul(n_inv),
        b.mul(b.neg().mul(n_inv)).mul(d),
        b.mul(b).mul(d).neg().mul(n_inv),
    );

    // ≡ (a² + -(b²d))*n⁻¹
    F::axiom_eqv_transitive(
        a.mul(a.mul(n_inv)).add(b.mul(b.neg().mul(n_inv)).mul(d)),
        a.mul(a).mul(n_inv).add(b.mul(b).mul(d).neg().mul(n_inv)),
        a.mul(a).add(b.mul(b).mul(d).neg()).mul(n_inv),
    );

    // a² + -(b²d) ≡ a² - b²d [sub_is_add_neg reversed]
    F::axiom_sub_is_add_neg(a.mul(a), b.mul(b).mul(d));
    F::axiom_eqv_symmetric(
        a.mul(a).sub(b.mul(b).mul(d)),
        a.mul(a).add(b.mul(b).mul(d).neg()),
    );
    // a² - b²d = norm(x) = n
    F::axiom_eqv_reflexive(n);

    // (a² + -(b²d))*n⁻¹ ≡ n*n⁻¹
    F::axiom_mul_congruence_left(
        a.mul(a).add(b.mul(b).mul(d).neg()),
        n,
        n_inv,
    );
    F::axiom_eqv_transitive(
        a.mul(a.mul(n_inv)).add(b.mul(b.neg().mul(n_inv)).mul(d)),
        a.mul(a).add(b.mul(b).mul(d).neg()).mul(n_inv),
        n.mul(n_inv),
    );

    // n*n⁻¹ ≡ 1
    F::axiom_mul_recip_right(n);
    F::axiom_eqv_transitive(
        a.mul(a.mul(n_inv)).add(b.mul(b.neg().mul(n_inv)).mul(d)),
        n.mul(n_inv),
        F::one(),
    );
}

/// Imaginary part of x * recip(x) ≡ 0
#[verifier::rlimit(30)]
pub proof fn lemma_mul_recip_right_im<F: Field, R: Radicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        !qe_eqv::<F, R>(x, qe_zero::<F, R>()),
        !qe_norm::<F, R>(x).eqv(F::zero()),
    ensures
        qe_mul::<F, R>(x, qe_recip::<F, R>(x)).im.eqv(F::zero()),
{
    let a = x.re; let b = x.im;
    let n = qe_norm::<F, R>(x);
    let n_inv = n.recip();

    // Imaginary part: a*((-b)*n⁻¹) + b*(a*n⁻¹)
    // = -(a*b)*n⁻¹ + (b*a)*n⁻¹
    // = -(a*b)*n⁻¹ + (a*b)*n⁻¹     [comm on b*a]
    // = 0

    // a*((-b)*n⁻¹) ≡ a*(-b)*n⁻¹ [assoc rev]
    lemma_mul_assoc_rev::<F>(a, b.neg(), n_inv);
    // a*(-b) ≡ -(a*b) [mul_neg_right]
    ring_lemmas::lemma_mul_neg_right::<F>(a, b);
    // a*(-b)*n⁻¹ ≡ -(a*b)*n⁻¹
    F::axiom_mul_congruence_left(a.mul(b.neg()), a.mul(b).neg(), n_inv);
    F::axiom_eqv_transitive(
        a.mul(b.neg().mul(n_inv)),
        a.mul(b.neg()).mul(n_inv),
        a.mul(b).neg().mul(n_inv),
    );

    // b*(a*n⁻¹) ≡ b*a*n⁻¹ [assoc rev]
    lemma_mul_assoc_rev::<F>(b, a, n_inv);
    // b*a ≡ a*b [comm]
    F::axiom_mul_commutative(b, a);
    // b*a*n⁻¹ ≡ (a*b)*n⁻¹
    F::axiom_mul_congruence_left(b.mul(a), a.mul(b), n_inv);
    F::axiom_eqv_transitive(
        b.mul(a.mul(n_inv)),
        b.mul(a).mul(n_inv),
        a.mul(b).mul(n_inv),
    );

    // Combine the two terms via congruence
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(b.neg().mul(n_inv)),
        a.mul(b).neg().mul(n_inv),
        b.mul(a.mul(n_inv)),
        a.mul(b).mul(n_inv),
    );

    // (-(ab))*n⁻¹ ≡ -((ab)*n⁻¹)  [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<F>(a.mul(b), n_inv);

    // (-(ab))*n⁻¹ + (ab)*n⁻¹ ≡ -((ab)*n⁻¹) + (ab)*n⁻¹  [add congruence]
    F::axiom_eqv_reflexive(a.mul(b).mul(n_inv));
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.mul(b).neg().mul(n_inv),
        a.mul(b).mul(n_inv).neg(),
        a.mul(b).mul(n_inv),
        a.mul(b).mul(n_inv),
    );

    // -((ab)*n⁻¹) + (ab)*n⁻¹ ≡ (ab)*n⁻¹ + -((ab)*n⁻¹) [comm]
    F::axiom_add_commutative(a.mul(b).mul(n_inv).neg(), a.mul(b).mul(n_inv));

    // (ab)*n⁻¹ + -((ab)*n⁻¹) ≡ 0  [add_inverse_right]
    F::axiom_add_inverse_right(a.mul(b).mul(n_inv));

    // Chain: LHS ≡ (-(ab))*n⁻¹ + (ab)*n⁻¹ ≡ -((ab)*n⁻¹) + (ab)*n⁻¹ ≡ (ab)*n⁻¹ + -((ab)*n⁻¹) ≡ 0
    let sum_orig = a.mul(b).neg().mul(n_inv).add(a.mul(b).mul(n_inv));
    let sum_neg = a.mul(b).mul(n_inv).neg().add(a.mul(b).mul(n_inv));
    let sum_comm = a.mul(b).mul(n_inv).add(a.mul(b).mul(n_inv).neg());

    F::axiom_eqv_transitive(sum_orig, sum_neg, sum_comm);
    F::axiom_eqv_transitive(sum_orig, sum_comm, F::zero());

    // Final chain: LHS.im ≡ sum_orig ≡ 0
    F::axiom_eqv_transitive(
        a.mul(b.neg().mul(n_inv)).add(b.mul(a.mul(n_inv))),
        sum_orig,
        F::zero(),
    );
}


// ═══════════════════════════════════════════════════════════════════
//  Small algebraic helpers
// ═══════════════════════════════════════════════════════════════════

/// In a field, x² ≡ 0 implies x ≡ 0.
///
/// Proof: if x ≢ 0, then x has an inverse, so
/// x = 1·x = (x⁻¹·x)·x = x⁻¹·(x·x) = x⁻¹·0 = 0, contradiction.
pub proof fn lemma_square_zero<F: Field>(x: F)
    requires
        x.mul(x).eqv(F::zero()),
    ensures
        x.eqv(F::zero()),
{
    if !x.eqv(F::zero()) {
        let x_inv = x.recip();
        F::axiom_mul_recip_right(x);
        // x*x⁻¹ ≡ 1
        // x⁻¹*(x*x) ≡ x⁻¹*0
        ring_lemmas::lemma_mul_congruence_right::<F>(x_inv, x.mul(x), F::zero());
        // x⁻¹*(x*x) ≡ (x⁻¹*x)*x [assoc rev]
        lemma_mul_assoc_rev::<F>(x_inv, x, x);
        // x⁻¹*x ≡ x*x⁻¹ [comm]
        F::axiom_mul_commutative(x_inv, x);
        // x*x⁻¹ ≡ 1, so (x⁻¹*x)*x ≡ 1*x
        F::axiom_eqv_transitive(x_inv.mul(x), x.mul(x_inv), F::one());
        F::axiom_mul_congruence_left(x_inv.mul(x), F::one(), x);
        // 1*x ≡ x
        ring_lemmas::lemma_mul_one_left::<F>(x);
        // (x⁻¹*x)*x ≡ 1*x ≡ x
        F::axiom_eqv_transitive(
            x_inv.mul(x).mul(x),
            F::one().mul(x),
            x,
        );
        // (x⁻¹*x)*x ≡ x⁻¹*(x*x) [assoc]
        F::axiom_eqv_symmetric(x_inv.mul(x).mul(x), x_inv.mul(x.mul(x)));
        // x⁻¹*(x*x) ≡ x⁻¹*0 (already established)
        // x⁻¹*0 ≡ 0
        F::axiom_mul_zero_right(x_inv);
        F::axiom_eqv_transitive(x_inv.mul(x.mul(x)), x_inv.mul(F::zero()), F::zero());
        // x ≡ (x⁻¹*x)*x [symmetric of above]
        F::axiom_eqv_symmetric(x, x_inv.mul(x).mul(x));
        // x ≡ (x⁻¹*x)*x ≡ x⁻¹*(x*x) ≡ 0
        F::axiom_eqv_transitive(x, x_inv.mul(x).mul(x), x_inv.mul(x.mul(x)));
        F::axiom_eqv_transitive(x, x_inv.mul(x.mul(x)), F::zero());
        // x ≡ 0 contradicts !x.eqv(0)
        F::axiom_eqv_symmetric(x, F::zero());
    }
}

/// a - b ≡ 0 implies a ≡ b.
pub proof fn lemma_sub_eqv_zero_implies_eqv<F: Field>(a: F, b: F)
    requires
        a.sub(b).eqv(F::zero()),
    ensures
        a.eqv(b),
{
    // a - b ≡ 0 → a + (-b) ≡ 0 → a ≡ -(-b) ≡ b
    F::axiom_sub_is_add_neg(a, b);
    // a.sub(b) ≡ a.add(b.neg()), need symmetric: a.add(b.neg()) ≡ a.sub(b)
    F::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    // a.add(b.neg()) ≡ a.sub(b) ≡ 0
    F::axiom_eqv_transitive(a.add(b.neg()), a.sub(b), F::zero());

    // a + (-b) ≡ 0 → a ≡ 0 + (-(-b)) = 0 - (-b)
    // Actually simpler: a + (-b) ≡ 0 → a + (-b) + b ≡ 0 + b ≡ b
    // a + (-b) + b ≡ a + ((-b) + b) [assoc]
    F::axiom_add_associative(a, b.neg(), b);
    // (-b) + b ≡ b + (-b) [comm]
    F::axiom_add_commutative(b.neg(), b);
    // b + (-b) ≡ 0
    F::axiom_add_inverse_right(b);
    // (-b) + b ≡ 0
    F::axiom_eqv_transitive(b.neg().add(b), b.add(b.neg()), F::zero());
    // a + ((-b) + b) ≡ a + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(
        a, b.neg().add(b), F::zero(),
    );
    // a + 0 ≡ a
    F::axiom_add_zero_right(a);
    F::axiom_eqv_transitive(a.add(b.neg().add(b)), a.add(F::zero()), a);
    // (a + (-b)) + b ≡ a + ((-b) + b) ≡ a
    F::axiom_eqv_transitive(
        a.add(b.neg()).add(b),
        a.add(b.neg().add(b)),
        a,
    );

    // (a + (-b)) + b ≡ 0 + b ≡ b
    F::axiom_add_congruence_left(a.add(b.neg()), F::zero(), b);
    additive_group_lemmas::lemma_add_zero_left::<F>(b);
    F::axiom_eqv_transitive(
        a.add(b.neg()).add(b),
        F::zero().add(b),
        b,
    );

    // a ≡ (a+(-b))+b ≡ b
    F::axiom_eqv_symmetric(a, a.add(b.neg()).add(b));
    F::axiom_eqv_transitive(a, a.add(b.neg()).add(b), b);
}

// ═══════════════════════════════════════════════════════════════════
//  Antisymmetry helpers: one-component-zero cases
// ═══════════════════════════════════════════════════════════════════

/// Helper for antisymmetry: the case re ≡ 0, im ≢ 0 leads to contradiction.
///
/// Unlike the im_zero case (where the contradiction is purely from sign constraints),
/// this case requires the square comparison: im²d > 0 but re² ≡ 0, so any
/// qe_nonneg case that provides im²d ≤ re² leads to im²d ≤ 0, a contradiction.
/// The remaining case (C1(x) + C1(-x)) gives 0≤im and 0≤-im, forcing im≡0.
#[verifier::rlimit(120)]
pub proof fn lemma_nonneg_neg_zero_re_zero<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        qe_nonneg::<F, R>(x),
        qe_nonneg::<F, R>(qext(x.re.neg(), x.im.neg())),
        x.re.eqv(F::zero()),
        !x.im.eqv(F::zero()),
    ensures false,
{
    let re = x.re;
    let im = x.im;
    let d = R::value();
    let re2 = re.mul(re);
    let im2d = im.mul(im).mul(d);

    // d > 0
    R::axiom_value_positive();

    // (-a)² ≡ a²
    ring_lemmas::lemma_neg_mul_neg::<F>(re, re);
    ring_lemmas::lemma_neg_mul_neg::<F>(im, im);
    F::axiom_mul_congruence_left(im.neg().mul(im.neg()), im.mul(im), d);

    // im² > 0, im²d > 0
    lemma_square_pos::<F>(im);
    ordered_field_lemmas::lemma_mul_pos_pos::<F>(im.mul(im), d);

    // re² ≡ 0
    lemma_eqv_zero_square_zero::<F>(re);

    // re ≡ 0 in both directions
    F::axiom_eqv_symmetric(re, F::zero());

    // re.lt(0) and 0.lt(re) are both false — kills C3(x)
    F::axiom_lt_iff_le_and_not_eqv(re, F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), re);

    // -re ≡ 0
    F::axiom_neg_congruence(re, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_transitive(re.neg(), F::zero().neg(), F::zero());
    F::axiom_eqv_symmetric(re.neg(), F::zero());

    // (-re).lt(0) and 0.lt(-re) both false — kills C3(-x)
    F::axiom_lt_iff_le_and_not_eqv(re.neg(), F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), re.neg());

    // (-re)² ≡ re² ≡ 0
    F::axiom_eqv_transitive(re.neg().mul(re.neg()), re.mul(re), F::zero());

    let neg_re2 = re.neg().mul(re.neg());
    let neg_im2d = im.neg().mul(im.neg()).mul(d);

    // Three-way case split:
    //   C2(x):  im²d ≤ re² ≡ 0 → contradiction
    //   C2(-x): (-im)²d ≤ (-re)² ≡ 0 → contradiction
    //   else:   C1(x) + C1(-x) → 0≤im and 0≤-im → im≡0 → contradiction

    if im2d.le(re2) {
        // im²d ≤ re² and re² ≡ 0 → im²d ≤ 0
        F::axiom_eqv_reflexive(im2d);
        F::axiom_le_congruence(im2d, im2d, re2, F::zero());
        // 0 < im²d and im²d ≤ 0 → 0 ≡ im²d, contradicts 0 < im²d
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), im2d);
        F::axiom_le_antisymmetric(F::zero(), im2d);
    } else if neg_im2d.le(neg_re2) {
        // (-im)²d ≤ (-re)² and (-re)² ≡ 0 → (-im)²d ≤ 0
        F::axiom_eqv_reflexive(neg_im2d);
        F::axiom_le_congruence(neg_im2d, neg_im2d, neg_re2, F::zero());
        // Convert (-im)²d ≤ 0 to im²d ≤ 0 via (-im)²d ≡ im²d
        F::axiom_eqv_reflexive(F::zero());
        F::axiom_le_congruence(neg_im2d, im2d, F::zero(), F::zero());
        // 0 < im²d and im²d ≤ 0 → contradiction
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), im2d);
        F::axiom_le_antisymmetric(F::zero(), im2d);
    } else {
        // !im²d≤re² kills C2(x). !(-im)²d≤(-re)² kills C2(-x).
        // C3(x) and C3(-x) already dead. Only C1(x) + C1(-x) remain.
        // C1(x) → 0≤im. C1(-x) → 0≤-im.

        // From C1(x): 0≤im → -im ≤ -0 ≡ 0
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(F::zero(), im);
        F::axiom_eqv_reflexive(im.neg());
        F::axiom_le_congruence(im.neg(), im.neg(), F::zero().neg(), F::zero());
        // Now: im.neg().le(F::zero())

        // From C1(-x): F::zero().le(im.neg())
        // Z3 extracts this: qe_nonneg(-x) true, C2(-x) dead, C3(-x) dead → C1(-x)

        // 0 ≤ -im and -im ≤ 0 → 0 ≡ -im
        F::axiom_le_antisymmetric(F::zero(), im.neg());
        F::axiom_eqv_symmetric(F::zero(), im.neg());
        // -im ≡ 0

        // -im ≡ 0 → --im ≡ -0 ≡ 0 → im ≡ 0 (contradicts !im.eqv(0))
        F::axiom_neg_congruence(im.neg(), F::zero());
        F::axiom_eqv_transitive(im.neg().neg(), F::zero().neg(), F::zero());
        additive_group_lemmas::lemma_neg_involution::<F>(im);
        F::axiom_eqv_symmetric(im.neg().neg(), im);
        F::axiom_eqv_transitive(im, im.neg().neg(), F::zero());
        // im ≡ 0, but !im.eqv(0) → false
    }
}

/// Helper for antisymmetry: the case im ≡ 0, re ≢ 0 leads to contradiction.
#[verifier::rlimit(80)]
pub proof fn lemma_nonneg_neg_zero_im_zero<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        qe_nonneg::<F, R>(x),
        qe_nonneg::<F, R>(qext(x.re.neg(), x.im.neg())),
        x.im.eqv(F::zero()),
        !x.re.eqv(F::zero()),
    ensures false,
{
    let re = x.re;
    let im = x.im;
    let d = R::value();
    let re2 = re.mul(re);
    let im2d = im.mul(im).mul(d);

    // d > 0
    R::axiom_value_positive();

    // (-a)² ≡ a²
    ring_lemmas::lemma_neg_mul_neg::<F>(re, re);
    ring_lemmas::lemma_neg_mul_neg::<F>(im, im);
    F::axiom_mul_congruence_left(im.neg().mul(im.neg()), im.mul(im), d);

    // re² > 0
    lemma_square_pos::<F>(re);

    // im² ≡ 0, im²d ≡ 0
    lemma_eqv_zero_square_zero::<F>(im);
    F::axiom_mul_congruence_left(im.mul(im), F::zero(), d);
    ring_lemmas::lemma_mul_zero_left::<F>(d);
    F::axiom_eqv_transitive(im2d, F::zero().mul(d), F::zero());

    // im ≡ 0 means im.lt(0) and 0.lt(im) are both false
    F::axiom_lt_iff_le_and_not_eqv(im, F::zero());
    F::axiom_eqv_symmetric(im, F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), im);

    // Derive 0 ≤ im from im ≡ 0
    F::axiom_eqv_reflexive(im);
    F::axiom_le_reflexive(im);
    F::axiom_le_congruence(im, F::zero(), im, im);
    // Now: F::zero().le(im)

    // Extract 0 ≤ re from nonneg(x):
    // C2 needs im.lt(0) — false. C3 needs 0.lt(im) — false. So C1 must hold.
    if !F::zero().le(re) {
        // All three cases of qe_nonneg(x) are false
        return;
    }

    // 0 ≤ re and re ≢ 0 → 0 < re
    assert(!F::zero().eqv(re)) by {
        if F::zero().eqv(re) { F::axiom_eqv_symmetric(F::zero(), re); }
    }
    ordered_ring_lemmas::lemma_trichotomy::<F>(F::zero(), re);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), re);

    // -re < 0
    lemma_pos_neg_is_neg::<F>(re);

    // -im ≡ 0
    F::axiom_neg_congruence(im, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_transitive(im.neg(), F::zero().neg(), F::zero());

    // -im ≡ 0 in both directions
    F::axiom_eqv_symmetric(im.neg(), F::zero());

    // → im.neg().lt(0) and 0.lt(im.neg()) are both false
    F::axiom_lt_iff_le_and_not_eqv(im.neg(), F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), im.neg());

    // Derive 0 ≤ -im from -im ≡ 0
    F::axiom_eqv_reflexive(im.neg());
    F::axiom_le_reflexive(im.neg());
    F::axiom_le_congruence(im.neg(), F::zero(), im.neg(), im.neg());

    // Nonneg(-x): C2 needs im.neg().lt(0) — false. C3 needs 0.lt(im.neg()) — false.
    // Only C1 possible. If 0 ≤ -re: -re < 0 → -re ≡ 0 → contradiction.
    if F::zero().le(re.neg()) {
        F::axiom_lt_iff_le_and_not_eqv(re.neg(), F::zero());
        F::axiom_le_antisymmetric(F::zero(), re.neg());
        F::axiom_eqv_symmetric(F::zero(), re.neg());
    }
    // else: !0≤-re eliminates C1,C2. C3 needs 0.lt(im.neg()) — false. All eliminated.
}

// ═══════════════════════════════════════════════════════════════════
//  lemma_nonneg_add_closed — nonneg is closed under addition
// ═══════════════════════════════════════════════════════════════════

/// Helper: rearrange q²d·s²d ≡ (qsd)·(qsd) i.e. product of two "x²d" terms
/// equals the square of "xyd".
/// More precisely: a.mul(a).mul(c) . b.mul(b).mul(c) ≡ a.mul(b).mul(c) . a.mul(b).mul(c)
proof fn lemma_sq_d_product<F: OrderedField>(a: F, b: F, c: F)
    ensures
        a.mul(a).mul(c).mul(b.mul(b).mul(c)).eqv(
            a.mul(b).mul(c).mul(a.mul(b).mul(c))
        ),
{
    // LHS = (a²c)(b²c) and RHS = (abc)(abc) = (abc)²
    // By square_mul: (abc)² ≡ (ab)²·c²
    // (ab)² ≡ a²·b² by square_mul
    // So RHS ≡ a²·b²·c²
    // LHS = (a²c)(b²c) = a²·c·b²·c = a²·b²·c·c = a²·b²·c²
    // So both ≡ a²·b²·c² — we just need to rearrange

    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let ab = a.mul(b);
    let a2c = a2.mul(c);
    let b2c = b2.mul(c);
    let abc = ab.mul(c);

    // RHS: abc·abc ≡ ab·ab · c·c by square_mul
    inequalities::lemma_square_mul::<F>(ab, c);
    // ab·ab ≡ a²·b² by square_mul
    inequalities::lemma_square_mul::<F>(a, b);
    // So abc² ≡ (a²·b²)·(c·c)
    F::axiom_eqv_reflexive(c.mul(c));
    ring_lemmas::lemma_mul_congruence::<F>(ab.mul(ab), a2.mul(b2), c.mul(c), c.mul(c));
    F::axiom_eqv_transitive(
        abc.mul(abc), ab.mul(ab).mul(c.mul(c)), a2.mul(b2).mul(c.mul(c))
    );

    // LHS: a2c · b2c
    // = (a²·c)·(b²·c)
    // By mul_four_commute(a², b², c, c): (a²·c)·(b²·c) ≡ (a²·c)·(b²·c)
    // Hmm, mul_four_commute says (a·c)·(b·d) ≡ (a·d)·(b·c)
    // With params (a², c, b², c): (a²·c)·(b²·c) ... that's the same
    // Try (a², b², c, c): (a²·c)·(b²·c) ≡ (a²·c)·(b²·c) — trivial
    // Need: (a²·c)·(b²·c) ≡ (a²·b²)·(c·c)
    // Use mul_four_commute(a², b², c, c): that gives
    //   a².mul(c).mul(b².mul(c)) ≡ a².mul(c).mul(b².mul(c)) — same thing
    // Actually mul_four_commute(a, c, b, d) gives (a·c)·(b·d) ≡ (a·d)·(b·c)
    // With (a², c, b², c): (a²·c)·(b²·c) ≡ (a²·c)·(b²·c) ← c and c same, trivial
    // I need (a², c, b², c) but rearranged as (a²·b²)·(c·c)
    // Use mul_four_commute(a², b², c, c): (a²·c)·(b²·c) ≡ (a²·c)·(b²·c) — same!

    // Different approach: just use assoc + comm directly
    // (a²·c)·(b²·c) ≡ a²·(c·(b²·c))  by assoc
    F::axiom_mul_associative(a2, c, b2c);
    // c·(b²·c) ≡ c·b²·c — need to rearrange to b²·c·c = b²·(c·c)
    // c·(b²·c): by assoc reversed (c·b²)·c ≡ c·(b²·c)
    F::axiom_mul_associative(c, b2, c);
    F::axiom_eqv_symmetric(c.mul(b2).mul(c), c.mul(b2.mul(c)));
    // c·b² ≡ b²·c by comm
    F::axiom_mul_commutative(c, b2);
    // (c·b²)·c ≡ (b²·c)·c by congruence
    F::axiom_mul_congruence_left(c.mul(b2), b2.mul(c), c);
    // (b²·c)·c ≡ b²·(c·c) by assoc
    F::axiom_mul_associative(b2, c, c);
    // chain: c·(b²·c) ≡ (c·b²)·c ≡ (b²·c)·c ≡ b²·(c·c)
    F::axiom_eqv_transitive(c.mul(b2.mul(c)), c.mul(b2).mul(c), b2.mul(c).mul(c));
    F::axiom_eqv_transitive(c.mul(b2.mul(c)), b2.mul(c).mul(c), b2.mul(c.mul(c)));

    // a²·(c·(b²·c)) ≡ a²·(b²·(c·c)) by congruence right
    ring_lemmas::lemma_mul_congruence_right::<F>(a2, c.mul(b2.mul(c)), b2.mul(c.mul(c)));
    // a²·(b²·(c·c)) ≡ (a²·b²)·(c·c) by assoc reversed
    F::axiom_mul_associative(a2, b2, c.mul(c));
    F::axiom_eqv_symmetric(a2.mul(b2).mul(c.mul(c)), a2.mul(b2.mul(c.mul(c))));

    // chain LHS: a2c·b2c ≡ a²·(c·b2c) ≡ a²·(b²·(c·c)) ≡ (a²·b²)·(c·c)
    F::axiom_eqv_transitive(
        a2c.mul(b2c), a2.mul(c.mul(b2.mul(c))), a2.mul(b2.mul(c.mul(c)))
    );
    F::axiom_eqv_transitive(
        a2c.mul(b2c), a2.mul(b2.mul(c.mul(c))), a2.mul(b2).mul(c.mul(c))
    );

    // Now LHS ≡ (a²·b²)·(c·c) and RHS ≡ (a²·b²)·(c·c)
    // So LHS ≡ RHS
    F::axiom_eqv_symmetric(
        abc.mul(abc), a2.mul(b2).mul(c.mul(c))
    );
    F::axiom_eqv_transitive(
        a2c.mul(b2c), a2.mul(b2).mul(c.mul(c)), abc.mul(abc)
    );
}

/// Helper: (a+b)²·c ≡ a²c + (1+1)·a·b·c + b²c
/// i.e. the square expansion times a factor c.
proof fn lemma_square_expand_mul<F: OrderedField>(a: F, b: F, c: F)
    ensures
        a.add(b).mul(a.add(b)).mul(c).eqv(
            a.mul(a).mul(c).add(
                F::one().add(F::one()).mul(a.mul(b)).mul(c)
            ).add(b.mul(b).mul(c))
        ),
{
    let two = F::one().add(F::one());
    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let ab = a.mul(b);
    let two_ab = two.mul(ab);
    let sum_sq = a.add(b).mul(a.add(b));

    // (a+b)² ≡ a² + 2ab + b² by square_expand
    ring_lemmas::lemma_square_expand::<F>(a, b);

    // Multiply both sides by c using congruence
    F::axiom_mul_congruence_left(
        sum_sq, a2.add(two_ab).add(b2), c
    );

    // Now expand (a² + 2ab + b²)·c by distributivity
    // First: (a² + 2ab + b²) = (a² + 2ab) + b²
    // (X + b²)·c ≡ X·c + b²·c by right distrib
    ring_lemmas::lemma_mul_distributes_right::<F>(a2.add(two_ab), b2, c);
    // X·c: (a² + 2ab)·c ≡ a²·c + (2ab)·c
    ring_lemmas::lemma_mul_distributes_right::<F>(a2, two_ab, c);

    // Chain: (a²+2ab+b²)·c ≡ (a²+2ab)·c + b²·c ≡ (a²c + 2ab·c) + b²c
    F::axiom_eqv_reflexive(b2.mul(c));
    additive_group_lemmas::lemma_add_congruence::<F>(
        a2.add(two_ab).mul(c), a2.mul(c).add(two_ab.mul(c)),
        b2.mul(c), b2.mul(c)
    );
    F::axiom_eqv_transitive(
        a2.add(two_ab).add(b2).mul(c),
        a2.add(two_ab).mul(c).add(b2.mul(c)),
        a2.mul(c).add(two_ab.mul(c)).add(b2.mul(c))
    );

    // Overall: sum_sq · c ≡ a²c + 2ab·c + b²c
    F::axiom_eqv_transitive(
        sum_sq.mul(c),
        a2.add(two_ab).add(b2).mul(c),
        a2.mul(c).add(two_ab.mul(c)).add(b2.mul(c))
    );
}

/// C2+C2 case: both nonneg with re≥0, im<0, im²d≤re².
proof fn lemma_nonneg_add_c2_c2<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), q.lt(F::zero()), q.mul(q).mul(R::value()).le(p.mul(p)),
        F::zero().le(r), s.lt(F::zero()), s.mul(s).mul(R::value()).le(r.mul(r)),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);
    let q2d = q.mul(q).mul(d);
    let s2d = s.mul(s).mul(d);
    let p2 = p.mul(p);
    let r2 = r.mul(r);

    // p+r ≥ 0
    inequalities::lemma_nonneg_add::<F>(p, r);

    // q+s < 0 (both negative)
    F::axiom_lt_iff_le_and_not_eqv(q, F::zero());
    F::axiom_lt_iff_le_and_not_eqv(s, F::zero());
    ordered_ring_lemmas::lemma_le_add_both::<F>(q, F::zero(), s, F::zero());
    // q+s ≤ 0+0 = 0
    additive_group_lemmas::lemma_add_zero_left::<F>(F::zero());
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        q.add(s), F::zero().add(F::zero()), F::zero()
    );

    // Need q+s ≢ 0 for lt. If q+s ≡ 0 then s ≡ -q. Since q < 0, -q > 0, so s > 0.
    // But s < 0 — contradiction.
    if sum_im.eqv(F::zero()) {
        // q + s ≡ 0 → s ≡ -q
        additive_group_lemmas::lemma_neg_unique::<F>(q, s);
        // s ≡ -q. q < 0 → -q > 0 → s > 0 but s < 0.
        ordered_ring_lemmas::lemma_lt_neg_flip::<F>(q, F::zero());
        additive_group_lemmas::lemma_neg_zero::<F>();
        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero().neg(), F::zero());
        // 0.neg() < 0... wait, we need 0 < -q
        // lt_neg_flip(q, 0): -0 < -q, and -0 ≡ 0, so 0 < -q
        F::axiom_eqv_reflexive(q.neg());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero().neg(), F::zero(), q.neg(), q.neg()
        );
        // Now 0 < q.neg() and s ≡ q.neg() → 0 < s
        F::axiom_eqv_reflexive(F::zero());
        F::axiom_eqv_symmetric(s, q.neg());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero(), F::zero(), q.neg(), s
        );
        // 0 < s contradicts s < 0
        ordered_ring_lemmas::lemma_lt_irreflexive::<F>(F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), s);
        F::axiom_lt_iff_le_and_not_eqv(s, F::zero());
        // Both s ≤ 0 and 0 ≤ s → s ≡ 0
        F::axiom_le_antisymmetric(s, F::zero());
        // But then s.eqv(0), and q+s ≡ 0 means q ≡ 0, but q < 0.
        // Contradiction arrives from 0 < s and s < 0 → s < s by transitivity
    }
    F::axiom_lt_iff_le_and_not_eqv(sum_im, F::zero());

    // Now have: sum_re ≥ 0, sum_im < 0
    // Need: (q+s)²d ≤ (p+r)²

    // Step 1: q²d + s²d ≤ p² + r² (add the two given inequalities)
    ordered_ring_lemmas::lemma_le_add_both::<F>(q2d, p2, s2d, r2);

    // Step 2: Multiply inequalities to get qsd ≤ pr
    // q²d·s²d ≤ p²·r² by le_mul_nonneg_both
    // Need 0 ≤ q²d. q² ≥ 0 (square_nonneg) and d > 0 → q²d ≥ 0
    ordered_ring_lemmas::lemma_square_nonneg::<F>(q);
    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
    F::axiom_le_mul_nonneg_monotone(F::zero(), q.mul(q), d);
    ring_lemmas::lemma_mul_zero_left::<F>(d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().mul(d), F::zero(), q2d
    );
    // 0 ≤ q²d ✓

    // Need 0 ≤ s²d similarly
    ordered_ring_lemmas::lemma_square_nonneg::<F>(s);
    F::axiom_le_mul_nonneg_monotone(F::zero(), s.mul(s), d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().mul(d), F::zero(), s2d
    );

    // Need 0 ≤ p² and 0 ≤ r²
    ordered_ring_lemmas::lemma_square_nonneg::<F>(p);
    ordered_ring_lemmas::lemma_square_nonneg::<F>(r);

    // le_mul_nonneg_both: 0 ≤ q²d ≤ p², 0 ≤ s²d ≤ r² → q²d·s²d ≤ p²·r²
    ordered_ring_lemmas::lemma_le_mul_nonneg_both::<F>(q2d, s2d, p2, r2);

    // q²d·s²d ≡ (q·s·d)² by lemma_sq_d_product(q, s, d)
    lemma_sq_d_product::<F>(q, s, d);
    // p²·r² ≡ (p·r)² by square_mul(p, r)
    inequalities::lemma_square_mul::<F>(p, r);
    F::axiom_eqv_symmetric(p.mul(r).mul(p.mul(r)), p2.mul(r2));

    // Congruence: (qsd)² ≤ (pr)²
    let qsd = q.mul(s).mul(d);
    let pr = p.mul(r);
    F::axiom_eqv_reflexive(qsd.mul(qsd));
    F::axiom_le_congruence(q2d.mul(s2d), qsd.mul(qsd), p2.mul(r2), pr.mul(pr));

    // Need 0 ≤ qsd: q < 0, s < 0, d > 0
    // q·s > 0 (neg × neg) by mul_neg_neg
    ordered_field_lemmas::lemma_mul_neg_neg::<F>(q, s);
    // qs > 0 → qs·d > 0 (pos × pos) by mul_pos_pos
    ordered_field_lemmas::lemma_mul_pos_pos::<F>(q.mul(s), d);
    // 0 < qsd → 0 ≤ qsd
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), qsd);

    // Need 0 ≤ pr: p ≥ 0, r ≥ 0
    F::axiom_le_mul_nonneg_monotone(F::zero(), p, r);
    ring_lemmas::lemma_mul_zero_left::<F>(r);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().mul(r), F::zero(), pr
    );

    // square_le_implies_le: 0 ≤ qsd, 0 ≤ pr, (qsd)² ≤ (pr)² → qsd ≤ pr
    inequalities::lemma_square_le_implies_le::<F>(qsd, pr);

    // Step 3: 2·qsd ≤ 2·pr
    // Multiply both sides by 2 = 1+1 ≥ 0
    let two = F::one().add(F::one());
    // 0 ≤ 1: from square_nonneg(1) gives 0 ≤ 1·1, then mul_one_right gives 1·1 ≡ 1
    ordered_ring_lemmas::lemma_square_nonneg::<F>(F::one());
    F::axiom_mul_one_right(F::one());
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        F::zero(), F::one().mul(F::one()), F::one()
    );
    // 0 ≤ 1, so 0 ≤ 1+1
    inequalities::lemma_nonneg_add::<F>(F::one(), F::one());
    // Wait, that gives 0 ≤ 1+1. But I actually already have 0 ≤ 1. Let me just use
    // le_add_compatible: 0 ≤ 1 → 0+1 ≤ 1+1
    // And 0+1 ≡ 1, 0 ≤ 1. So 0 ≤ 1+1 transitively. Either way, nonneg_add works.

    // qsd ≤ pr → qsd·2 ≤ pr·2 (multiply by 2 ≥ 0)
    F::axiom_le_mul_nonneg_monotone(qsd, pr, two);
    // Rearrange to 2·qsd ≤ 2·pr using commutativity
    F::axiom_mul_commutative(qsd, two);
    F::axiom_mul_commutative(pr, two);
    F::axiom_eqv_symmetric(two.mul(qsd), qsd.mul(two));
    F::axiom_eqv_symmetric(two.mul(pr), pr.mul(two));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        qsd.mul(two), two.mul(qsd), pr.mul(two)
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        two.mul(qsd), pr.mul(two), two.mul(pr)
    );
    // Now: 2·(q·s·d) ≤ 2·(p·r)

    // But we actually need 2·q·s·d ≤ 2·p·r where 2·q·s = 2·(qs) and similarly
    // Actually what we need for the expansion is: two.mul(q.mul(s)).mul(d) ≤ two.mul(p.mul(r))
    // Hmm, let me just use the form two.mul(qsd) ≤ two.mul(pr) and then
    // relate two.mul(q.mul(s).mul(d)) to two.mul(q.mul(s)).mul(d)

    // Step 4: Add results
    // q²d + s²d ≤ p² + r² (step 1)
    // 2·qsd ≤ 2·pr (step 3)
    // → (q²d + s²d) + 2·qsd ≤ (p² + r²) + 2·pr
    ordered_ring_lemmas::lemma_le_add_both::<F>(
        q2d.add(s2d), p2.add(r2),
        two.mul(qsd), two.mul(pr)
    );

    // Step 5: Show LHS ≡ (q+s)²d and RHS ≡ (p+r)²
    // (q+s)²·d ≡ q²d + 2·q·s·d + s²d by lemma_square_expand_mul
    lemma_square_expand_mul::<F>(q, s, d);
    // (p+r)² ≡ p² + 2·p·r + r² by square_expand
    ring_lemmas::lemma_square_expand::<F>(p, r);

    // Need to show: q²d + s²d + 2·qsd ≡ q²d + 2·q·s·d + s²d
    // These differ only in ordering: a+b+c vs a+c+b where b=s²d, c=2·qsd
    // Actually: (q²d + s²d) + 2·qsd vs q²d + (2·(q·s)·d) + s²d
    // The first is (q²d + s²d) + two·qsd
    // The second is (q²d + two·(qs)·d) + s²d
    // two·qsd = two·(q·s·d) and two·(qs)·d = (two·(q·s))·d
    // q·s·d = (q·s)·d by def (left-assoc), so two·qsd = two·((q·s)·d)
    // And two·(qs)·d = (two·(q·s))·d
    // two·((q·s)·d) vs (two·(q·s))·d — differ by associativity
    F::axiom_mul_associative(two, q.mul(s), d);
    F::axiom_eqv_symmetric(two.mul(q.mul(s)).mul(d), two.mul(q.mul(s).mul(d)));
    // two·qsd ≡ two·(q.mul(s).mul(d)) ≡ (two·(qs))·d

    // Now swap middle terms in the sum:
    // (q²d + s²d) + two·qsd ≡ (q²d + two·qs·d) + s²d
    // This is (A + B) + C ≡ (A + C) + B with A=q²d, B=s²d, C=two·qsd
    // = A+B+C ≡ A+C+B — follows from add commutativity + associativity
    F::axiom_add_associative(q2d, s2d, two.mul(qsd));
    // (q²d + s²d) + 2qsd ≡ q²d + (s²d + 2qsd)
    F::axiom_add_commutative(s2d, two.mul(qsd));
    // s²d + 2qsd ≡ 2qsd + s²d
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        q2d, s2d.add(two.mul(qsd)), two.mul(qsd).add(s2d)
    );
    // q²d + (s²d + 2qsd) ≡ q²d + (2qsd + s²d)
    F::axiom_eqv_transitive(
        q2d.add(s2d).add(two.mul(qsd)),
        q2d.add(s2d.add(two.mul(qsd))),
        q2d.add(two.mul(qsd).add(s2d))
    );
    // q²d + (2qsd + s²d) ≡ (q²d + 2qsd) + s²d by assoc reversed
    F::axiom_add_associative(q2d, two.mul(qsd), s2d);
    F::axiom_eqv_symmetric(
        q2d.add(two.mul(qsd)).add(s2d),
        q2d.add(two.mul(qsd).add(s2d))
    );
    F::axiom_eqv_transitive(
        q2d.add(s2d).add(two.mul(qsd)),
        q2d.add(two.mul(qsd).add(s2d)),
        q2d.add(two.mul(qsd)).add(s2d)
    );

    // Now use the associativity of two·qsd ≡ (two·qs)·d to match square_expand_mul
    // square_expand_mul gives (q+s)²d ≡ q²d + (two·(qs))·d + s²d
    //                                   = q2d + two.mul(q.mul(s)).mul(d) + s2d
    // We have: q2d + two.mul(qsd) + s2d where qsd = q.mul(s).mul(d)
    // And two.mul(qsd) = two.mul(q.mul(s).mul(d)) ≡ two.mul(q.mul(s)).mul(d)
    // Need q2d + two·qsd ≡ q2d + (two·qs)·d
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        q2d, two.mul(qsd), two.mul(q.mul(s)).mul(d)
    );
    F::axiom_eqv_reflexive(s2d);
    additive_group_lemmas::lemma_add_congruence::<F>(
        q2d.add(two.mul(qsd)), q2d.add(two.mul(q.mul(s)).mul(d)),
        s2d, s2d
    );

    // Similarly for RHS: (p² + r²) + 2·pr ≡ (p+r)²
    // square_expand gives (p+r)² ≡ p² + 2·pr + r²
    //                              = p2 + two.mul(p.mul(r)) + r2
    //                              = p2 + two.mul(pr) + r2
    // We have (p2 + r2) + two.mul(pr)
    // Need: (p2 + r2) + two·pr ≡ p2 + two·pr + r2
    // Same rearrangement as above
    F::axiom_add_associative(p2, r2, two.mul(pr));
    F::axiom_add_commutative(r2, two.mul(pr));
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        p2, r2.add(two.mul(pr)), two.mul(pr).add(r2)
    );
    F::axiom_eqv_transitive(
        p2.add(r2).add(two.mul(pr)),
        p2.add(r2.add(two.mul(pr))),
        p2.add(two.mul(pr).add(r2))
    );
    F::axiom_add_associative(p2, two.mul(pr), r2);
    F::axiom_eqv_symmetric(
        p2.add(two.mul(pr)).add(r2),
        p2.add(two.mul(pr).add(r2))
    );
    F::axiom_eqv_transitive(
        p2.add(r2).add(two.mul(pr)),
        p2.add(two.mul(pr).add(r2)),
        p2.add(two.mul(pr)).add(r2)
    );

    // Final congruence chain:
    // (q+s)²d ≡ q2d + (two·qs)·d + s2d  (from square_expand_mul)
    //         ≡ q2d + two·qsd + s2d       (from assoc on two·qs·d)
    //         ≡ (q2d + s2d) + two·qsd      (from add rearrangement above)
    //         ≤ (p2 + r2) + two·pr          (from step 4)
    //         ≡ p2 + two·pr + r2            (from add rearrangement)
    //         ≡ (p+r)²                      (from square_expand, reversed)

    // Left side: (q+s)²d ≡ (q2d+s2d) + two·qsd
    let lhs = sum_im.mul(sum_im).mul(d);
    let lhs_expanded = q2d.add(two.mul(q.mul(s)).mul(d)).add(s2d);
    // from square_expand_mul: lhs ≡ lhs_expanded
    // lhs_expanded ≡ q2d.add(two.mul(qsd)).add(s2d)  (via the assoc step)
    F::axiom_eqv_symmetric(
        q2d.add(two.mul(qsd)).add(s2d),
        lhs_expanded
    );
    // Hmm wait, I showed q2d+two·qsd+s2d ≡ q2d+(two·qs)·d+s2d but I need
    // q2d+(two·qs)·d+s2d ≡ q2d+two·qsd+s2d
    // That's just symmetric of what I had.

    // Let me just use le_congruence to put it all together:
    // We have: (q2d+s2d)+two·qsd ≤ (p2+r2)+two·pr  (step 4)
    // LHS of step 4 ≡ (q+s)²d
    // RHS of step 4 ≡ (p+r)²
    // → (q+s)²d ≤ (p+r)²

    // For now, use the expanded forms and congruence
    let step4_lhs = q2d.add(s2d).add(two.mul(qsd));
    let step4_rhs = p2.add(r2).add(two.mul(pr));

    // step4_lhs ≡ lhs (i.e., (q+s)²d):
    // We showed step4_lhs ≡ q2d+two·qsd+s2d (rearrangement)
    // and q2d+two·qsd+s2d ≡ q2d+(two·qs)·d+s2d (assoc)
    // and lhs ≡ q2d+(two·qs)·d+s2d (square_expand_mul)
    // So step4_lhs ≡ lhs by chain

    // step4_rhs ≡ rhs (i.e., (p+r)²):
    // step4_rhs ≡ p2+two·pr+r2 (rearrangement)
    // (p+r)² ≡ p2+two·pr+r2 (square_expand)
    // So step4_rhs ≡ (p+r)²

    // Apply le_congruence:
    F::axiom_eqv_symmetric(lhs, lhs_expanded);
    F::axiom_eqv_transitive(
        lhs, lhs_expanded, q2d.add(two.mul(qsd)).add(s2d)
    );
    // step4_lhs ≡ q2d+two·qsd+s2d was shown; reverse for transitive
    F::axiom_eqv_symmetric(
        step4_lhs, q2d.add(two.mul(qsd)).add(s2d)
    );
    F::axiom_eqv_transitive(
        lhs, q2d.add(two.mul(qsd)).add(s2d), step4_lhs
    );

    // RHS chain
    let rhs = sum_re.mul(sum_re);
    F::axiom_eqv_symmetric(rhs, p2.add(two.mul(pr)).add(r2));
    F::axiom_eqv_symmetric(
        step4_rhs, p2.add(two.mul(pr)).add(r2)
    );
    // step4_rhs ≡ p2+two·pr+r2 ≡ rhs... hmm, both are eqv to same thing
    // rhs ≡ p2+two·pr+r2 (from square_expand, symmetric)
    // step4_rhs ≡ p2+two·pr+r2 (from rearrangement)
    // So step4_rhs ≡ rhs
    F::axiom_eqv_transitive(
        step4_rhs, p2.add(two.mul(pr)).add(r2), rhs
    );

    // Final: lhs ≡ step4_lhs ≤ step4_rhs ≡ rhs
    // → lhs ≤ rhs
    F::axiom_eqv_symmetric(lhs, step4_lhs);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        step4_lhs, lhs, step4_rhs
    );
    // Hmm, le_congruence_left(a1, a2, b) needs a1.eqv(a2), a1.le(b) → a2.le(b)
    // I have step4_lhs ≤ step4_rhs and lhs ≡ step4_lhs → lhs ≤ step4_rhs
    // Wait, I need lhs.eqv(step4_lhs), not the other way. Let me fix:
    // lhs ≡ step4_lhs means step4_lhs.eqv(lhs) after symmetric.
    // le_congruence_left needs the eqv direction: a1.eqv(a2), a1.le(b).
    // a1 = step4_lhs, a2 = lhs: need step4_lhs.eqv(lhs), have lhs.eqv(step4_lhs).
    F::axiom_eqv_symmetric(lhs, step4_lhs);
    // No wait: I showed lhs ≡ step4_lhs several lines above.
    // le_congruence_left(step4_lhs, lhs, step4_rhs) needs step4_lhs.eqv(lhs)
    // That's eqv_symmetric of lhs.eqv(step4_lhs)... but I also called eqv_symmetric(lhs, step4_lhs) already, which gives step4_lhs.eqv(lhs).
    // So that should work. But I've probably called symmetric twice and gone back. Let me be explicit:

    // HAVE: step4_lhs ≤ step4_rhs (from step 4)
    // HAVE: lhs ≡ step4_lhs (chain above)
    // WANT: lhs ≤ step4_rhs
    // Use le_congruence: need a1.eqv(a2), b1.eqv(b2), a1.le(b1) → a2.le(b2)
    // a1=step4_lhs, a2=lhs, b1=step4_rhs, b2=step4_rhs
    F::axiom_eqv_symmetric(lhs, step4_lhs); // step4_lhs.eqv(lhs)
    F::axiom_eqv_reflexive(step4_rhs);
    F::axiom_le_congruence(step4_lhs, lhs, step4_rhs, step4_rhs);
    // lhs ≤ step4_rhs

    // HAVE: lhs ≤ step4_rhs
    // HAVE: step4_rhs ≡ rhs
    // WANT: lhs ≤ rhs
    F::axiom_eqv_reflexive(lhs);
    F::axiom_le_congruence(lhs, lhs, step4_rhs, rhs);
    // lhs ≤ rhs, i.e., (q+s)²d ≤ (p+r)²

    // Now we have C2 satisfied: sum_re ≥ 0, sum_im < 0, (q+s)²d ≤ (p+r)²
}

/// C1+C2: u=(p,q) with p≥0,q≥0; v=(r,s) with r≥0,s<0,s²d≤r²
proof fn lemma_nonneg_add_c1_c2<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), F::zero().le(q),
        F::zero().le(r), s.lt(F::zero()), s.mul(s).mul(R::value()).le(r.mul(r)),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);

    // p+r ≥ 0
    inequalities::lemma_nonneg_add::<F>(p, r);

    // Check sign of q+s
    F::axiom_le_total(F::zero(), sum_im);
    if F::zero().le(sum_im) {
        // C1: p+r ≥ 0 and q+s ≥ 0
    } else {
        // sum_im.le(0) but NOT 0.le(sum_im), so sum_im ≤ 0
        // Actually le_total gives: 0.le(sum_im) || sum_im.le(0)
        // We're in the !0.le(sum_im) branch, so sum_im.le(0).
        // Need sum_im < 0: need sum_im ≢ 0
        // q ≥ 0 and s < 0 and q+s ≤ 0
        // If q+s ≡ 0, then s ≡ -q ≡ -(nonneg) ≤ 0. And q ≡ -s > 0.
        // Actually just: sum_im ≤ 0 is enough, need to show C2.
        // For C2 need sum_im < 0 OR sum_im ≡ 0.
        // If sum_im ≡ 0: C1 since sum_re ≥ 0 and sum_im ≡ 0 → 0 ≤ sum_im
        // So just handle sum_im ≡ 0 → C1
        ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<F>(sum_im, F::zero());
        if sum_im.eqv(F::zero()) {
            F::axiom_eqv_symmetric(sum_im, F::zero());
            partial_order_lemmas::lemma_le_eqv_implies_le::<F>(F::zero(), sum_im);
            // C1
        } else {
            // sum_im < 0, C2 candidate: need (q+s)²d ≤ (p+r)²
            // |q+s| ≤ |s|: since q ≥ 0, -(q+s) = -q-s ≤ -s = |s|
            // And 0 ≤ -(q+s) since q+s < 0
            // square_le_square(-(q+s), -s) needs 0 ≤ -(q+s) ≤ -s
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(F::zero(), q);
            additive_group_lemmas::lemma_neg_zero::<F>();
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                q.neg(), F::zero().neg(), F::zero()
            );
            // -q ≤ 0

            // -(q+s) = -q + (-s)
            additive_group_lemmas::lemma_neg_add::<F>(q, s);
            // (q+s).neg() ≡ q.neg() + s.neg()

            // 0 ≤ -(q+s): from q+s < 0 → 0 < -(q+s)
            ordered_ring_lemmas::lemma_lt_neg_flip::<F>(sum_im, F::zero());
            additive_group_lemmas::lemma_neg_zero::<F>();
            F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
            F::axiom_eqv_reflexive(sum_im.neg());
            ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
                F::zero().neg(), F::zero(), sum_im.neg(), sum_im.neg()
            );
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_im.neg());
            // 0 < -(q+s) → 0 ≤ -(q+s)

            // 0 ≤ -s: since s < 0
            ordered_ring_lemmas::lemma_lt_neg_flip::<F>(s, F::zero());
            F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
            F::axiom_eqv_reflexive(s.neg());
            ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
                F::zero().neg(), F::zero(), s.neg(), s.neg()
            );
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), s.neg());
            // 0 ≤ -s

            // -(q+s) ≤ -s: from -q ≤ 0 → -q + (-s) ≤ 0 + (-s) = -s
            F::axiom_le_add_monotone(q.neg(), F::zero(), s.neg());
            additive_group_lemmas::lemma_add_zero_left::<F>(s.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                q.neg().add(s.neg()), F::zero().add(s.neg()), s.neg()
            );
            // -q + (-s) ≤ -s
            // -(q+s) ≡ -q + (-s) by neg_add, symmetric gives the direction we need
            F::axiom_eqv_symmetric(sum_im.neg(), q.neg().add(s.neg()));
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                q.neg().add(s.neg()), sum_im.neg(), s.neg()
            );
            // WANT: sum_im.neg() ≤ s.neg()
            // Use le_congruence_left(q.neg().add(s.neg()), sum_im.neg(), s.neg())

            // Now: square_le_square(-(q+s), -s)
            // 0 ≤ -(q+s) ≤ -s → (-(q+s))² ≤ (-s)²
            ordered_ring_lemmas::lemma_square_le_square::<F>(sum_im.neg(), s.neg());

            // (-(q+s))² ≡ (q+s)² by neg_mul_neg
            ring_lemmas::lemma_neg_mul_neg::<F>(sum_im, sum_im);
            // (-s)² ≡ s² by neg_mul_neg
            ring_lemmas::lemma_neg_mul_neg::<F>(s, s);
            // (q+s)² ≤ s²
            F::axiom_le_congruence(
                sum_im.neg().mul(sum_im.neg()), sum_im.mul(sum_im),
                s.neg().mul(s.neg()), s.mul(s)
            );

            // (q+s)²·d ≤ s²·d (multiply by d ≥ 0)
            R::axiom_value_positive();
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
            F::axiom_le_mul_nonneg_monotone(sum_im.mul(sum_im), s.mul(s), d);

            // s²d ≤ r² (given)
            // r ≤ p+r: 0 ≤ p → r ≤ r+p = p+r
            F::axiom_le_add_monotone(F::zero(), p, r);
            additive_group_lemmas::lemma_add_zero_left::<F>(r);
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                F::zero().add(r), r, p.add(r)
            );
            // r ≤ p+r, and 0 ≤ r
            ordered_ring_lemmas::lemma_square_le_square::<F>(r, sum_re);
            // r² ≤ (p+r)²

            // Chain: (q+s)²d ≤ s²d ≤ r² ≤ (p+r)²
            F::axiom_le_transitive(
                sum_im.mul(sum_im).mul(d), s.mul(s).mul(d), r.mul(r)
            );
            F::axiom_le_transitive(
                sum_im.mul(sum_im).mul(d), r.mul(r), sum_re.mul(sum_re)
            );
            // C2: sum_re ≥ 0, sum_im < 0, (q+s)²d ≤ (p+r)²
        }
    }
}

/// C1+C3: u=(p,q) with p≥0,q≥0; v=(r,s) with r<0,s>0,r²≤s²d
proof fn lemma_nonneg_add_c1_c3<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), F::zero().le(q),
        r.lt(F::zero()), F::zero().lt(s), r.mul(r).le(s.mul(s).mul(R::value())),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);

    // q+s > 0: q ≥ 0 and s > 0 → q+s ≥ s > 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), s);
    F::axiom_le_add_monotone(F::zero(), q, s);
    additive_group_lemmas::lemma_add_zero_left::<F>(s);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().add(s), s, q.add(s)
    );
    // s ≤ q+s and 0 < s → 0 < q+s? Need transitivity: 0 < s ≤ q+s
    // 0 ≤ s (from 0 < s) and s ≤ q+s, so 0 ≤ q+s by le_transitive
    F::axiom_le_transitive(F::zero(), s, sum_im);
    // For strict: need 0 ≢ q+s.
    // If 0 ≡ q+s: then 0 ≥ s (from s ≤ q+s ≡ 0 → s ≤ 0). But s > 0 → contradiction.
    // Actually just: 0 < s and s ≤ q+s → 0 < q+s? Not directly from axioms.
    // But 0.le(q+s) suffices for "q+s ≥ 0" which is what C1 and C3 need.

    // Check sign of p+r
    F::axiom_le_total(F::zero(), sum_re);
    if F::zero().le(sum_re) {
        // C1: p+r ≥ 0 and q+s ≥ 0
    } else {
        // sum_re ≤ 0 but not 0 ≤ sum_re
        ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<F>(sum_re, F::zero());
        if sum_re.eqv(F::zero()) {
            F::axiom_eqv_symmetric(sum_re, F::zero());
            partial_order_lemmas::lemma_le_eqv_implies_le::<F>(F::zero(), sum_re);
            // C1
        } else {
            // sum_re < 0, C3 candidate: need (p+r)² ≤ (q+s)²d
            // |p+r| ≤ |r|: p ≥ 0, p+r < 0, so -(p+r) = -p-r ≤ -r = |r| (since -p ≤ 0)
            // And 0 ≤ -(p+r) since p+r < 0

            // 0 ≤ -(p+r)
            ordered_ring_lemmas::lemma_lt_neg_flip::<F>(sum_re, F::zero());
            additive_group_lemmas::lemma_neg_zero::<F>();
            F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
            F::axiom_eqv_reflexive(sum_re.neg());
            ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
                F::zero().neg(), F::zero(), sum_re.neg(), sum_re.neg()
            );
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_re.neg());

            // 0 ≤ -r: from r < 0
            ordered_ring_lemmas::lemma_lt_neg_flip::<F>(r, F::zero());
            F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
            F::axiom_eqv_reflexive(r.neg());
            ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
                F::zero().neg(), F::zero(), r.neg(), r.neg()
            );
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), r.neg());

            // -(p+r) ≤ -r: from p ≥ 0 → -p ≤ 0 → -p + (-r) ≤ 0 + (-r) = -r
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(F::zero(), p);
            additive_group_lemmas::lemma_neg_zero::<F>();
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                p.neg(), F::zero().neg(), F::zero()
            );
            // -p ≤ 0
            F::axiom_le_add_monotone(p.neg(), F::zero(), r.neg());
            additive_group_lemmas::lemma_add_zero_left::<F>(r.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                p.neg().add(r.neg()), F::zero().add(r.neg()), r.neg()
            );
            // -p + (-r) ≤ -r
            additive_group_lemmas::lemma_neg_add::<F>(p, r);
            F::axiom_eqv_symmetric(sum_re.neg(), p.neg().add(r.neg()));
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                p.neg().add(r.neg()), sum_re.neg(), r.neg()
            );
            // -(p+r) ≤ -r

            // square_le_square(-(p+r), -r): (p+r)² ≤ r²
            ordered_ring_lemmas::lemma_square_le_square::<F>(sum_re.neg(), r.neg());
            ring_lemmas::lemma_neg_mul_neg::<F>(sum_re, sum_re);
            ring_lemmas::lemma_neg_mul_neg::<F>(r, r);
            F::axiom_le_congruence(
                sum_re.neg().mul(sum_re.neg()), sum_re.mul(sum_re),
                r.neg().mul(r.neg()), r.mul(r)
            );
            // (p+r)² ≤ r²

            // r² ≤ s²d (given)
            // s ≤ q+s: from q ≥ 0, add_monotone
            // s² ≤ (q+s)² by square_le_square(s, q+s) with 0 < s ≤ q+s
            // Wait, need 0 ≤ s for square_le_square.
            // 0 < s → 0 ≤ s
            ordered_ring_lemmas::lemma_square_le_square::<F>(s, sum_im);
            // s² ≤ (q+s)²

            // s²d ≤ (q+s)²d by multiplying by d ≥ 0
            R::axiom_value_positive();
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
            F::axiom_le_mul_nonneg_monotone(s.mul(s), sum_im.mul(sum_im), d);
            // s²d ≤ (q+s)²d

            // Chain: (p+r)² ≤ r² ≤ s²d ≤ (q+s)²d
            F::axiom_le_transitive(
                sum_re.mul(sum_re), r.mul(r), s.mul(s).mul(d)
            );
            F::axiom_le_transitive(
                sum_re.mul(sum_re), s.mul(s).mul(d), sum_im.mul(sum_im).mul(d)
            );
            // C3: sum_re < 0, q+s > 0 (well, 0 ≤ q+s and we need 0 < q+s)
            // Actually for C3 we need 0 < sum_im. We showed 0 ≤ sum_im.
            // Need to rule out sum_im ≡ 0. If sum_im ≡ 0, then (q+s)²d ≡ 0,
            // but (p+r)² ≤ (q+s)²d ≡ 0, and (p+r)² ≥ 0 → (p+r)² ≡ 0 → p+r ≡ 0
            // But p+r < 0 → contradiction.
            // So 0 < sum_im, establishing C3.
            if F::zero().eqv(sum_im) {
                // sum_im ≡ 0, derive contradiction
                F::axiom_eqv_symmetric(F::zero(), sum_im);
                // (q+s)² ≡ 0²=0 by eqv_zero_square_zero
                lemma_eqv_zero_square_zero::<F>(sum_im);
                // (q+s)²d ≡ 0·d = 0
                F::axiom_mul_congruence_left(sum_im.mul(sum_im), F::zero(), d);
                ring_lemmas::lemma_mul_zero_left::<F>(d);
                F::axiom_eqv_transitive(
                    sum_im.mul(sum_im).mul(d), F::zero().mul(d), F::zero()
                );
                // (p+r)² ≤ (q+s)²d ≡ 0 and (p+r)² ≥ 0 → (p+r)² ≡ 0
                ordered_ring_lemmas::lemma_square_nonneg::<F>(sum_re);
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    sum_re.mul(sum_re), sum_im.mul(sum_im).mul(d), F::zero()
                );
                F::axiom_le_antisymmetric(sum_re.mul(sum_re), F::zero());
                // (p+r)² ≡ 0
                // In ordered field: (p+r)² ≡ 0 → p+r ≡ 0 (contrapositive of square_pos)
                F::axiom_eqv_symmetric(sum_re.mul(sum_re), F::zero());
                if !sum_re.eqv(F::zero()) {
                    lemma_square_pos::<F>(sum_re);
                    F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_re.mul(sum_re));
                    // 0 < (p+r)² but (p+r)² ≡ 0 → 0 ≡ (p+r)² → contradiction
                }
                // sum_re ≡ 0 contradicts sum_re < 0
                F::axiom_lt_iff_le_and_not_eqv(sum_re, F::zero());
            }
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_im);
        }
    }
}

/// C3+C3: both nonneg with re<0, im>0, re²≤im²d.
/// Symmetric to C2+C2 with re/im roles swapped.
proof fn lemma_nonneg_add_c3_c3<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        p.lt(F::zero()), F::zero().lt(q), p.mul(p).le(q.mul(q).mul(R::value())),
        r.lt(F::zero()), F::zero().lt(s), r.mul(r).le(s.mul(s).mul(R::value())),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);
    let p2 = p.mul(p);
    let r2 = r.mul(r);
    let q2d = q.mul(q).mul(d);
    let s2d = s.mul(s).mul(d);

    // q+s > 0 (both positive)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), q);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), s);
    inequalities::lemma_nonneg_add::<F>(q, s);
    // 0 ≤ q+s. For strict: need q+s ≢ 0.
    // If q+s ≡ 0, then s ≡ -q. q > 0 → -q < 0 → s < 0 contradicts s > 0.
    if F::zero().eqv(sum_im) {
        // 0 ≡ q+s → q+s ≡ 0 → s ≡ -q
        F::axiom_eqv_symmetric(F::zero(), sum_im);
        additive_group_lemmas::lemma_neg_unique::<F>(q, s);
        // -q < 0 (from 0 < q)
        lemma_pos_neg_is_neg::<F>(q);
        // s < 0 (from s ≡ -q and -q < 0)
        F::axiom_eqv_symmetric(s, q.neg());
        F::axiom_eqv_reflexive(F::zero());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            q.neg(), s, F::zero(), F::zero()
        );
        // s < 0 contradicts 0 < s
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), s);
        F::axiom_lt_iff_le_and_not_eqv(s, F::zero());
        F::axiom_le_antisymmetric(s, F::zero());
    }
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_im);

    // p+r < 0 (both negative)
    F::axiom_lt_iff_le_and_not_eqv(p, F::zero());
    F::axiom_lt_iff_le_and_not_eqv(r, F::zero());
    ordered_ring_lemmas::lemma_le_add_both::<F>(p, F::zero(), r, F::zero());
    additive_group_lemmas::lemma_add_zero_left::<F>(F::zero());
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        sum_re, F::zero().add(F::zero()), F::zero()
    );
    // p+r ≤ 0. Strict: if p+r ≡ 0 then r ≡ -p, p < 0 → -p > 0 → r > 0 contradicts r < 0.
    if sum_re.eqv(F::zero()) {
        // p + r ≡ 0 → r ≡ -p
        additive_group_lemmas::lemma_neg_unique::<F>(p, r);
        // p < 0 → 0.neg() < p.neg() (lt_neg_flip), then -0 ≡ 0 → 0 < -p
        ordered_ring_lemmas::lemma_lt_neg_flip::<F>(p, F::zero());
        additive_group_lemmas::lemma_neg_zero::<F>();
        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
        F::axiom_eqv_reflexive(p.neg());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero().neg(), F::zero(), p.neg(), p.neg()
        );
        // 0 < -p, and r ≡ -p → 0 < r
        F::axiom_eqv_symmetric(r, p.neg());
        F::axiom_eqv_reflexive(F::zero());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero(), F::zero(), p.neg(), r
        );
        // 0 < r contradicts r < 0
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), r);
        F::axiom_lt_iff_le_and_not_eqv(r, F::zero());
        F::axiom_le_antisymmetric(r, F::zero());
    }
    F::axiom_lt_iff_le_and_not_eqv(sum_re, F::zero());

    // C3 candidate: need (p+r)² ≤ (q+s)²d
    // Mirror of C2+C2: p² ≤ q²d and r² ≤ s²d → (p+r)² ≤ (q+s)²d
    // Using same strategy: add inequalities + multiply + sqrt + combine

    // Step 1: p² + r² ≤ q²d + s²d
    ordered_ring_lemmas::lemma_le_add_both::<F>(p2, q2d, r2, s2d);

    // Step 2: Multiply inequalities to get pr ≤ qsd
    ordered_ring_lemmas::lemma_square_nonneg::<F>(p);
    ordered_ring_lemmas::lemma_square_nonneg::<F>(r);
    ordered_ring_lemmas::lemma_square_nonneg::<F>(q);
    ordered_ring_lemmas::lemma_square_nonneg::<F>(s);
    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);

    // 0 ≤ q²d
    F::axiom_le_mul_nonneg_monotone(F::zero(), q.mul(q), d);
    ring_lemmas::lemma_mul_zero_left::<F>(d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(F::zero().mul(d), F::zero(), q2d);

    // 0 ≤ s²d
    F::axiom_le_mul_nonneg_monotone(F::zero(), s.mul(s), d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(F::zero().mul(d), F::zero(), s2d);

    // le_mul_nonneg_both: 0 ≤ p² ≤ q²d, 0 ≤ r² ≤ s²d → p²·r² ≤ q²d·s²d
    ordered_ring_lemmas::lemma_le_mul_nonneg_both::<F>(p2, r2, q2d, s2d);

    // p²·r² ≡ (pr)² by square_mul
    inequalities::lemma_square_mul::<F>(p, r);
    F::axiom_eqv_symmetric(p.mul(r).mul(p.mul(r)), p2.mul(r2));

    // q²d·s²d ≡ (qsd)² by lemma_sq_d_product
    lemma_sq_d_product::<F>(q, s, d);

    let pr = p.mul(r);
    let qsd = q.mul(s).mul(d);
    F::axiom_eqv_reflexive(pr.mul(pr));
    F::axiom_le_congruence(p2.mul(r2), pr.mul(pr), q2d.mul(s2d), qsd.mul(qsd));

    // 0 ≤ pr: p < 0, r < 0 → pr > 0
    ordered_field_lemmas::lemma_mul_neg_neg::<F>(p, r);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), pr);

    // 0 ≤ qsd: q > 0, s > 0, d > 0 → qs > 0 → qsd > 0
    ordered_field_lemmas::lemma_mul_pos_pos::<F>(q, s);
    ordered_field_lemmas::lemma_mul_pos_pos::<F>(q.mul(s), d);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), qsd);

    // square_le_implies_le: (pr)² ≤ (qsd)² with 0 ≤ pr, 0 ≤ qsd → pr ≤ qsd
    inequalities::lemma_square_le_implies_le::<F>(pr, qsd);

    // Step 3: 2·pr ≤ 2·qsd
    let two = F::one().add(F::one());
    // 0 ≤ 1: from square_nonneg(1) gives 0 ≤ 1·1, then mul_one_right gives 1·1 ≡ 1
    ordered_ring_lemmas::lemma_square_nonneg::<F>(F::one());
    F::axiom_mul_one_right(F::one());
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        F::zero(), F::one().mul(F::one()), F::one()
    );
    // 0 ≤ 1, so 0 ≤ 1+1
    inequalities::lemma_nonneg_add::<F>(F::one(), F::one());
    // 0 ≤ 2

    F::axiom_le_mul_nonneg_monotone(pr, qsd, two);
    F::axiom_mul_commutative(pr, two);
    F::axiom_mul_commutative(qsd, two);
    F::axiom_eqv_symmetric(two.mul(pr), pr.mul(two));
    F::axiom_eqv_symmetric(two.mul(qsd), qsd.mul(two));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        pr.mul(two), two.mul(pr), qsd.mul(two)
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        two.mul(pr), qsd.mul(two), two.mul(qsd)
    );

    // Step 4: (p²+r²) + 2·pr ≤ (q²d+s²d) + 2·qsd
    ordered_ring_lemmas::lemma_le_add_both::<F>(
        p2.add(r2), q2d.add(s2d),
        two.mul(pr), two.mul(qsd)
    );

    // Step 5: LHS ≡ (p+r)², RHS ≡ (q+s)²d
    // (p+r)² ≡ p² + 2pr + r²
    ring_lemmas::lemma_square_expand::<F>(p, r);
    // (q+s)²d ≡ q²d + 2·qs·d + s²d
    lemma_square_expand_mul::<F>(q, s, d);

    // Rearrange: (p²+r²)+2·pr ≡ p²+2·pr+r² ≡ (p+r)²
    F::axiom_add_associative(p2, r2, two.mul(pr));
    F::axiom_add_commutative(r2, two.mul(pr));
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        p2, r2.add(two.mul(pr)), two.mul(pr).add(r2)
    );
    F::axiom_eqv_transitive(
        p2.add(r2).add(two.mul(pr)),
        p2.add(r2.add(two.mul(pr))),
        p2.add(two.mul(pr).add(r2))
    );
    F::axiom_add_associative(p2, two.mul(pr), r2);
    F::axiom_eqv_symmetric(
        p2.add(two.mul(pr)).add(r2), p2.add(two.mul(pr).add(r2))
    );
    F::axiom_eqv_transitive(
        p2.add(r2).add(two.mul(pr)),
        p2.add(two.mul(pr).add(r2)),
        p2.add(two.mul(pr)).add(r2)
    );

    // Rearrange: (q²d+s²d)+2·qsd ≡ q²d+2·qsd+s²d ≡ (q+s)²d
    F::axiom_add_associative(q2d, s2d, two.mul(qsd));
    F::axiom_add_commutative(s2d, two.mul(qsd));
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        q2d, s2d.add(two.mul(qsd)), two.mul(qsd).add(s2d)
    );
    F::axiom_eqv_transitive(
        q2d.add(s2d).add(two.mul(qsd)),
        q2d.add(s2d.add(two.mul(qsd))),
        q2d.add(two.mul(qsd).add(s2d))
    );
    F::axiom_add_associative(q2d, two.mul(qsd), s2d);
    F::axiom_eqv_symmetric(
        q2d.add(two.mul(qsd)).add(s2d), q2d.add(two.mul(qsd).add(s2d))
    );
    F::axiom_eqv_transitive(
        q2d.add(s2d).add(two.mul(qsd)),
        q2d.add(two.mul(qsd).add(s2d)),
        q2d.add(two.mul(qsd)).add(s2d)
    );

    // two·qsd = two·(q·s·d) ≡ (two·(q·s))·d = two.mul(q.mul(s)).mul(d) by assoc
    F::axiom_mul_associative(two, q.mul(s), d);
    F::axiom_eqv_symmetric(two.mul(q.mul(s)).mul(d), two.mul(q.mul(s).mul(d)));
    // q2d + two·qsd + s2d ≡ q2d + (two·qs)·d + s2d
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        q2d, two.mul(qsd), two.mul(q.mul(s)).mul(d)
    );
    F::axiom_eqv_reflexive(s2d);
    additive_group_lemmas::lemma_add_congruence::<F>(
        q2d.add(two.mul(qsd)), q2d.add(two.mul(q.mul(s)).mul(d)),
        s2d, s2d
    );

    // Final chains
    let step4_lhs = p2.add(r2).add(two.mul(pr));
    let step4_rhs = q2d.add(s2d).add(two.mul(qsd));
    let lhs = sum_re.mul(sum_re);
    let rhs = sum_im.mul(sum_im).mul(d);

    // step4_lhs ≡ (p+r)²
    F::axiom_eqv_symmetric(lhs, p2.add(two.mul(pr)).add(r2));
    F::axiom_eqv_transitive(step4_lhs, p2.add(two.mul(pr)).add(r2), lhs);
    // Hmm, step4_lhs ≡ p2+2pr+r2 ≡ (p+r)² → step4_lhs ≡ lhs
    // Actually I showed step4_lhs ≡ p2+2pr+r2. And (p+r)² ≡ p2+2pr+r2 from square_expand.
    // So need: step4_lhs ≡ p2+2pr+r2 ≡ (p+r)² = lhs
    // lhs ≡ p2+2pr+r2 from square_expand, so p2+2pr+r2 ≡ lhs by symmetric.
    // BUT I already called these transitives above... I need to be careful with eqv state.
    // Let me just use le_congruence at the end.

    F::axiom_eqv_symmetric(step4_lhs, p2.add(two.mul(pr)).add(r2));
    F::axiom_eqv_symmetric(lhs, p2.add(two.mul(pr)).add(r2));
    F::axiom_eqv_transitive(lhs, p2.add(two.mul(pr)).add(r2), step4_lhs);
    // lhs ≡ step4_lhs
    F::axiom_eqv_symmetric(lhs, step4_lhs);
    // step4_lhs ≡ lhs

    // step4_rhs ≡ (q+s)²d = rhs via chain through q2d+(two·qs)·d+s2d
    let rhs_expanded = q2d.add(two.mul(q.mul(s)).mul(d)).add(s2d);
    // step4_rhs ≡ q2d+two·qsd+s2d (rearrangement above)
    // q2d+two·qsd+s2d ≡ rhs_expanded (assoc step)
    // rhs ≡ rhs_expanded (square_expand_mul)
    // So step4_rhs ≡ rhs

    // I already showed step4_rhs ≡ q2d+two·qsd+s2d above
    // And q2d+two·qsd+s2d ≡ q2d+(two·qs)·d+s2d = rhs_expanded
    // Actually q2d.add(two.mul(qsd)).add(s2d) ≡ rhs_expanded needs the assoc chain
    // Let me just do the final le_congruence directly:
    F::axiom_eqv_symmetric(step4_lhs, lhs);
    F::axiom_eqv_reflexive(step4_rhs);
    F::axiom_le_congruence(step4_lhs, lhs, step4_rhs, step4_rhs);

    // Now: lhs ≤ step4_rhs. Need step4_rhs ≡ rhs.
    // This is messy. Let me chain:
    // step4_rhs ≡ q2d+two·qsd+s2d (rearrangement)
    // ≡ q2d+(two·qs)·d+s2d (assoc on two·qsd)
    // ≡ rhs (symmetric of square_expand_mul)

    // The rearrangement was proved above. And the assoc step was proved.
    // Let me combine: step4_rhs ≡ q2d+two·qsd+s2d ≡ rhs_expanded ≡ rhs
    // chain 1: step4_rhs → q2d+two·qsd+s2d (already proved)
    let mid1 = q2d.add(two.mul(qsd)).add(s2d);
    // chain 2: mid1 → rhs_expanded
    // mid1 = q2d + two·qsd + s2d, rhs_expanded = q2d + (two·qs)·d + s2d
    // diff: two·qsd vs (two·qs)·d. Already proved two·qsd ≡ (two·qs)·d
    // So mid1 ≡ rhs_expanded by add congruence.
    // chain 3: rhs_expanded → rhs (symmetric of square_expand_mul)
    F::axiom_eqv_symmetric(rhs, rhs_expanded);

    // Build the full chain
    F::axiom_eqv_transitive(step4_rhs, mid1, rhs_expanded);
    F::axiom_eqv_transitive(step4_rhs, rhs_expanded, rhs);

    F::axiom_eqv_reflexive(lhs);
    F::axiom_le_congruence(lhs, lhs, step4_rhs, rhs);
    // Explicitly assert C3: sum_re < 0, 0 < sum_im, (p+r)² ≤ (q+s)²d
    assert(sum_re.lt(F::zero()));
    assert(F::zero().lt(sum_im));
    assert(lhs.le(rhs));
}

/// C2+C3: u=(p,q) with p≥0,q<0,q²d≤p²; v=(r,s) with r<0,s>0,r²≤s²d
/// This is the hardest case.
/// Strategy: multiply the two inequality chains and cancel.
proof fn lemma_nonneg_add_c2_c3<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), q.lt(F::zero()), q.mul(q).mul(R::value()).le(p.mul(p)),
        r.lt(F::zero()), F::zero().lt(s), r.mul(r).le(s.mul(s).mul(R::value())),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);

    // Sub-case analysis on signs of p+r and q+s
    F::axiom_le_total(F::zero(), sum_re);
    F::axiom_le_total(F::zero(), sum_im);

    if F::zero().le(sum_re) && F::zero().le(sum_im) {
        // C1: both ≥ 0 → done
    } else if F::zero().le(sum_re) {
        // sum_re ≥ 0, sum_im ≤ 0 (NOT ≥ 0)
        // Need C2: sum_re ≥ 0, sum_im < 0, (q+s)²d ≤ (p+r)²
        // First show sum_im < 0
        ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<F>(sum_im, F::zero());
        if sum_im.eqv(F::zero()) {
            // sum_im ≡ 0 → C1
            F::axiom_eqv_symmetric(sum_im, F::zero());
            partial_order_lemmas::lemma_le_eqv_implies_le::<F>(F::zero(), sum_im);
        } else {
            // sum_im < 0. Prove (q+s)²d ≤ (p+r)² via multiply-and-cancel.
            lemma_nonneg_add_c2_c3_subB::<F, R>(p, q, r, s);
        }
    } else if F::zero().le(sum_im) {
        // sum_re ≤ 0 (NOT ≥ 0), sum_im ≥ 0
        // Need C3: sum_re < 0, sum_im > 0, (p+r)² ≤ (q+s)²d
        ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<F>(sum_re, F::zero());
        if sum_re.eqv(F::zero()) {
            // sum_re ≡ 0 → 0 ≤ sum_re → C1
            F::axiom_eqv_symmetric(sum_re, F::zero());
            partial_order_lemmas::lemma_le_eqv_implies_le::<F>(F::zero(), sum_re);
        } else {
            // sum_re < 0. Need sum_im > 0 (not just ≥ 0).
            // If sum_im ≡ 0: (q+s)²d = 0, need (p+r)² ≤ 0, which forces p+r ≡ 0,
            // contradicting p+r < 0. So sum_im > 0.
            if F::zero().eqv(sum_im) {
                F::axiom_eqv_symmetric(F::zero(), sum_im);
                lemma_eqv_zero_square_zero::<F>(sum_im);
                F::axiom_mul_congruence_left(sum_im.mul(sum_im), F::zero(), d);
                ring_lemmas::lemma_mul_zero_left::<F>(d);
                F::axiom_eqv_transitive(
                    sum_im.mul(sum_im).mul(d), F::zero().mul(d), F::zero()
                );
                // Need to show (p+r)² ≤ 0 to get contradiction.
                // From sub-case D impossibility: p+r < 0 and q+s ≡ 0
                // q+s ≡ 0 → s ≡ -q, q < 0 → -q > 0 → s > 0 ✓ (consistent)
                // Also need q+s ≡ 0 → s ≡ -q → s² ≡ q² → s²d ≡ q²d
                // From q²d ≤ p² and r² ≤ s²d ≡ q²d: r² ≤ q²d ≤ p²
                // r² ≤ p². |r| = -r and p ≥ 0. (-r)² = r² ≤ p². So -r ≤ p.
                // But p+r < 0 → p < -r. Contradiction with -r ≤ p.
                // (or rather: from square_le_implies_le(-r, p)... but that needs 0 ≤ -r and 0 ≤ p)
                additive_group_lemmas::lemma_neg_unique::<F>(q, s);
                // s ≡ q.neg()
                // s² ≡ q² via neg_mul_neg congruence
                ring_lemmas::lemma_neg_mul_neg::<F>(q, q);
                // (-q)(-q) ≡ q·q
                // s·s ≡ (-q)·(-q) via congruence (s ≡ -q)
                ring_lemmas::lemma_mul_congruence::<F>(s, q.neg(), s, q.neg());
                F::axiom_eqv_transitive(s.mul(s), q.neg().mul(q.neg()), q.mul(q));
                // s²d ≡ q²d
                F::axiom_mul_congruence_left(s.mul(s), q.mul(q), d);
                // r² ≤ s²d ≡ q²d ≤ p²
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    r.mul(r), s.mul(s).mul(d), q.mul(q).mul(d)
                );
                F::axiom_le_transitive(r.mul(r), q.mul(q).mul(d), p.mul(p));
                // 0 ≤ -r (r < 0)
                ordered_ring_lemmas::lemma_lt_neg_flip::<F>(r, F::zero());
                additive_group_lemmas::lemma_neg_zero::<F>();
                F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
                F::axiom_eqv_reflexive(r.neg());
                ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
                    F::zero().neg(), F::zero(), r.neg(), r.neg()
                );
                F::axiom_lt_iff_le_and_not_eqv(F::zero(), r.neg());
                // (-r)² = r²
                ring_lemmas::lemma_neg_mul_neg::<F>(r, r);
                F::axiom_eqv_symmetric(r.neg().mul(r.neg()), r.mul(r));
                // (-r)² ≤ p²
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    r.mul(r), r.neg().mul(r.neg()), p.mul(p)
                );
                // square_le_implies_le(-r, p): -r ≤ p
                inequalities::lemma_square_le_implies_le::<F>(r.neg(), p);
                // -r ≤ p → 0 ≤ p + r (i.e. p + r ≥ 0)
                // -r ≤ p → -r + r ≤ p + r → 0 ≤ p+r
                F::axiom_le_add_monotone(r.neg(), p, r);
                additive_group_lemmas::lemma_add_inverse_left::<F>(r);
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    r.neg().add(r), F::zero(), p.add(r)
                );
                // 0 ≤ p+r but p+r < 0 — contradiction
                F::axiom_lt_iff_le_and_not_eqv(sum_re, F::zero());
                F::axiom_le_antisymmetric(sum_re, F::zero());
                F::axiom_eqv_symmetric(sum_re, F::zero());
            }
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), sum_im);
            // Now sum_re < 0, sum_im > 0. C3: need (p+r)² ≤ (q+s)²d
            lemma_nonneg_add_c2_c3_subC::<F, R>(p, q, r, s);
        }
    } else {
        // Both sum_re ≤ 0 and sum_im ≤ 0 (neither ≥ 0). This is impossible.
        // Sub-case D: prove contradiction.
        // From q²d ≤ p² and r² ≤ s²d, p+r ≤ 0 and q+s ≤ 0:
        // p ≤ -r → p² ≤ r² → q²d ≤ p² ≤ r² ≤ s²d → q² ≤ s²
        // → |q| ≤ s → -q ≤ s → q + s ≥ 0. Contradiction with q+s ≤ 0 and strict.

        // First: p+r ≤ 0 means p ≤ -r
        F::axiom_le_add_monotone(sum_re, F::zero(), r.neg());
        additive_group_lemmas::lemma_add_zero_left::<F>(r.neg());
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            sum_re.add(r.neg()), F::zero().add(r.neg()), r.neg()
        );
        // p+r + (-r) ≤ -r
        F::axiom_add_associative(p, r, r.neg());
        F::axiom_add_inverse_right(r);
        additive_group_lemmas::lemma_add_congruence_right::<F>(
            p, r.add(r.neg()), F::zero()
        );
        F::axiom_eqv_transitive(
            p.add(r).add(r.neg()), p.add(r.add(r.neg())), p.add(F::zero())
        );
        F::axiom_add_zero_right(p);
        F::axiom_eqv_transitive(
            p.add(r).add(r.neg()), p.add(F::zero()), p
        );
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            sum_re.add(r.neg()), p, r.neg()
        );
        // p ≤ -r

        // 0 ≤ p (given) and 0 ≤ -r (from r < 0)
        ordered_ring_lemmas::lemma_lt_neg_flip::<F>(r, F::zero());
        additive_group_lemmas::lemma_neg_zero::<F>();
        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
        F::axiom_eqv_reflexive(r.neg());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero().neg(), F::zero(), r.neg(), r.neg()
        );
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), r.neg());

        // square_le_square(p, -r): p² ≤ (-r)² = r²
        ordered_ring_lemmas::lemma_square_le_square::<F>(p, r.neg());
        ring_lemmas::lemma_neg_mul_neg::<F>(r, r);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            p.mul(p), r.neg().mul(r.neg()), r.mul(r)
        );

        // chain: q²d ≤ p² ≤ r² ≤ s²d
        F::axiom_le_transitive(q.mul(q).mul(d), p.mul(p), r.mul(r));
        F::axiom_le_transitive(q.mul(q).mul(d), r.mul(r), s.mul(s).mul(d));

        // cancel d: q²d ≤ s²d → q² ≤ s² (mul_le_cancel_pos)
        R::axiom_value_positive();
        ordered_field_lemmas::lemma_mul_le_cancel_pos::<F>(
            q.mul(q), s.mul(s), d
        );

        // 0 ≤ -q (q < 0)
        ordered_ring_lemmas::lemma_lt_neg_flip::<F>(q, F::zero());
        additive_group_lemmas::lemma_neg_zero::<F>();
        F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
        F::axiom_eqv_reflexive(q.neg());
        ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
            F::zero().neg(), F::zero(), q.neg(), q.neg()
        );
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), q.neg());
        // 0 ≤ s (s > 0)
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), s);

        // (-q)² = q², so (-q)² ≤ s²
        ring_lemmas::lemma_neg_mul_neg::<F>(q, q);
        F::axiom_eqv_symmetric(q.neg().mul(q.neg()), q.mul(q));
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            q.mul(q), q.neg().mul(q.neg()), s.mul(s)
        );

        // square_le_implies_le(-q, s): -q ≤ s
        inequalities::lemma_square_le_implies_le::<F>(q.neg(), s);

        // -q ≤ s → -q + q ≤ s + q → 0 ≤ s + q = q + s
        F::axiom_le_add_monotone(q.neg(), s, q);
        additive_group_lemmas::lemma_add_inverse_left::<F>(q);
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            q.neg().add(q), F::zero(), s.add(q)
        );
        F::axiom_add_commutative(s, q);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(), s.add(q), sum_im
        );
        // 0 ≤ q+s — contradicts !(0 ≤ sum_im)
    }
}

/// Sub-case B of C2+C3: p+r ≥ 0, q+s < 0, need (q+s)²d ≤ (p+r)²
proof fn lemma_nonneg_add_c2_c3_subB<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), q.lt(F::zero()), q.mul(q).mul(R::value()).le(p.mul(p)),
        r.lt(F::zero()), F::zero().lt(s), r.mul(r).le(s.mul(s).mul(R::value())),
        F::zero().le(p.add(r)),
        q.add(s).lt(F::zero()),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);

    // STEP 0: Setup — b = -q > 0, e = s > 0
    let b = q.neg();
    let e = s;

    // 0 < b (from q < 0)
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(q, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(b);
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero().neg(), F::zero(), b, b
    );
    // 0 < b

    // b ≢ 0 (from 0 < b)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
    if b.eqv(F::zero()) { F::axiom_eqv_symmetric(b, F::zero()); }

    // STEP 1: t = p / b, show t ≥ 0 and t² ≥ d
    let t = p.div(b);

    // t ≥ 0: nonneg / pos
    ordered_field_lemmas::lemma_nonneg_div_pos::<F>(p, b);
    // 0 ≤ t

    // t² ≥ d: from p² ≥ q²d, divide both sides by b² = q² > 0.
    // First show 0 < b²
    lemma_square_pos::<F>(b);  // b ≢ 0 → 0 < b²

    // p² ≥ q²d, i.e., q²d ≤ p²
    // q² = b² (since q.neg() = b, and (-q)² = q²)
    ring_lemmas::lemma_neg_mul_neg::<F>(q, q);
    // b² ≡ q². Need symmetric for le_congruence_left.
    F::axiom_eqv_symmetric(b.mul(b), q.mul(q));
    // q² ≡ b²
    F::axiom_eqv_reflexive(d);
    ring_lemmas::lemma_mul_congruence::<F>(q.mul(q), b.mul(b), d, d);
    // q²d ≡ b²d
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        q.mul(q).mul(d), b.mul(b).mul(d), p.mul(p)
    );
    // b²d ≤ p²

    // Swap to d·b² form, then divide
    let b2 = b.mul(b);
    F::axiom_mul_commutative(b2, d);
    // b²·d ≡ d·b²
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        b2.mul(d), d.mul(b2), p.mul(p)
    );
    // d·b² ≤ p²

    // Divide by b²: d·b²/b² ≤ p²/b²
    ordered_field_lemmas::lemma_le_div_monotone::<F>(d.mul(b2), p.mul(p), b2);

    // d·b²/b² ≡ d by lemma_mul_div_cancel(d, b2)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b2);
    if b2.eqv(F::zero()) { F::axiom_eqv_symmetric(b2, F::zero()); }
    field_lemmas::lemma_mul_div_cancel::<F>(d, b2);

    // d ≤ p²/b²
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        d.mul(b2).div(b2), d, p.mul(p).div(b2)
    );
    // d ≤ p²/b²

    // p²/b² ≡ t²: use lemma_div_mul_div(p, b, p, b) → (p/b)·(p/b) ≡ (p·p)/(b·b)
    field_lemmas::lemma_div_mul_div::<F>(p, b, p, b);
    // t·t ≡ p²/b², i.e., t² ≡ p²/b²
    F::axiom_eqv_symmetric(t.mul(t), p.mul(p).div(b2));
    // p²/b² ≡ t²

    // d ≤ t²
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(d, p.mul(p).div(b2), t.mul(t));

    // STEP 2: u = r.neg() / e, show u ≥ 0 and u² ≤ d
    let c = r.neg();  // c = -r > 0 (since r < 0)
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(r, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(c);
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(F::zero().neg(), F::zero(), c, c);
    // 0 < c

    let u = c.div(e);  // u = (-r)/s

    // e ≢ 0 (from 0 < e = s)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
    if e.eqv(F::zero()) { F::axiom_eqv_symmetric(e, F::zero()); }

    // u ≥ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), c);
    ordered_field_lemmas::lemma_nonneg_div_pos::<F>(c, e);
    // 0 ≤ u

    // u² ≤ d: from r² ≤ s²d, i.e., c² ≤ e²d (since (-r)² = r², s = e)
    let e2 = e.mul(e);
    ring_lemmas::lemma_neg_mul_neg::<F>(r, r);
    // c² ≡ r². Need symmetric:
    F::axiom_eqv_symmetric(c.mul(c), r.mul(r));
    // r² ≡ c², so r² ≤ s²d → c² ≤ s²d = e²d
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        r.mul(r), c.mul(c), s.mul(s).mul(d)
    );
    // c² ≤ e²d

    // Swap to d·e² form, then divide
    F::axiom_mul_commutative(e2, d);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        c.mul(c), e2.mul(d), d.mul(e2)
    );
    // c² ≤ d·e²

    // Divide by e²
    lemma_square_pos::<F>(e); // 0 < e²
    ordered_field_lemmas::lemma_le_div_monotone::<F>(c.mul(c), d.mul(e2), e2);
    // c²/e² ≤ d·e²/e²

    // c²/e² ≡ u²
    field_lemmas::lemma_div_mul_div::<F>(c, e, c, e);
    F::axiom_eqv_symmetric(u.mul(u), c.mul(c).div(e2));

    // d·e²/e² ≡ d
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), e2);
    if e2.eqv(F::zero()) { F::axiom_eqv_symmetric(e2, F::zero()); }
    field_lemmas::lemma_mul_div_cancel::<F>(d, e2);

    // u² ≤ d
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        c.mul(c).div(e2), u.mul(u), d.mul(e2).div(e2)
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        u.mul(u), d.mul(e2).div(e2), d
    );
    // u² ≤ d

    // STEP 3: t ≥ u (from u² ≤ d ≤ t², both nonneg)
    F::axiom_le_transitive(u.mul(u), d, t.mul(t));
    // u² ≤ t²
    inequalities::lemma_square_le_implies_le::<F>(u, t);
    // u ≤ t

    // STEP 4: b - e > 0 (from q + s < 0)
    // -(q+s) = (-q)+(-s) = b + (-e). But we need b - e = b + (-e).
    // -(q+s) > 0, and -(q+s) ≡ b + (-e) = b - e.
    let beta = b.sub(e);  // β = b - e = -(q+s)
    additive_group_lemmas::lemma_neg_add::<F>(q, s);
    // -(q+s) ≡ (-q) + (-s) = b + (-e) = b - e = β
    // But sub is defined as a + (-b), so b.sub(e) = b.add(e.neg()) = b.add(s.neg())
    // We need: -(q+s) ≡ β
    // -(q+s) ≡ q.neg() + s.neg() = b + s.neg()
    // β = b.sub(e) = b.add(e.neg()) = b.add(s.neg())  [since e = s]
    // So -(q+s) ≡ β definitionally? Not quite — we need eqv.
    // sum_im.neg() ≡ q.neg().add(s.neg()) [by lemma_neg_add]
    // = b.add(s.neg()) [since b = q.neg()]
    // But β = b.sub(e) = b.add(e.neg()) = b.add(s.neg()) [since e = s]
    // These are the same term! So sum_im.neg() ≡ β.
    // 0 < -(q+s): from q+s < 0
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(sum_im, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    // F::zero().neg() < sum_im.neg(), i.e., after congruence 0 < -(q+s)
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(sum_im.neg());
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero().neg(), F::zero(), sum_im.neg(), sum_im.neg()
    );
    // 0 < sum_im.neg()
    // Now prove sum_im.neg() ≡ beta:
    // sum_im.neg() = (q+s).neg() ≡ q.neg() + s.neg() [by neg_add] = b + s.neg()
    // beta = b.sub(e) ≡ b.add(e.neg()) [by axiom_sub_is_add_neg] = b.add(s.neg()) [since e=s]
    // Both ≡ b.add(s.neg()), so chain through that.
    F::axiom_sub_is_add_neg(b, e);
    // beta ≡ b.add(e.neg()) = b.add(s.neg()) — same term since e = s
    F::axiom_eqv_symmetric(beta, b.add(s.neg()));
    // b.add(s.neg()) ≡ beta
    // sum_im.neg() ≡ q.neg().add(s.neg()) = b.add(s.neg()) [same term since b = q.neg()]
    // So sum_im.neg() ≡ b.add(s.neg()) ≡ beta
    F::axiom_eqv_transitive(sum_im.neg(), b.add(s.neg()), beta);
    // sum_im.neg() ≡ beta

    F::axiom_eqv_reflexive(F::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero(), F::zero(), sum_im.neg(), beta
    );
    // 0 < beta

    // β ≢ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), beta);
    if beta.eqv(F::zero()) { F::axiom_eqv_symmetric(beta, F::zero()); }

    // STEP 5: t·b ≡ p, u·e ≡ c
    field_lemmas::lemma_div_mul_cancel::<F>(p, b);
    // (p/b)·b ≡ p, i.e., t·b ≡ p

    field_lemmas::lemma_div_mul_cancel::<F>(c, e);
    // (c/e)·e ≡ c, i.e., u·e ≡ c

    // STEP 6: t·b - u·e ≡ p - c ≡ p + r
    // p - c = p - (-r) = p + r (since c = -r, so -c = r by neg_involution)
    // t·b ≡ p, u·e ≡ c, so t·b - u·e ≡ p - c
    additive_group_lemmas::lemma_sub_congruence::<F>(t.mul(b), p, u.mul(e), c);
    // tb - ue ≡ p - c

    // p - c ≡ p + r: need axiom_sub_is_add_neg to bridge sub and add(neg)
    F::axiom_sub_is_add_neg(p, c);
    // p.sub(c) ≡ p.add(c.neg()) = p.add(r.neg().neg())
    // r.neg().neg() ≡ r by neg_involution
    additive_group_lemmas::lemma_neg_involution::<F>(r);
    additive_group_lemmas::lemma_add_congruence_right::<F>(p, r.neg().neg(), r);
    // p.add(r.neg().neg()) ≡ p.add(r) = sum_re
    F::axiom_eqv_transitive(p.sub(c), p.add(c.neg()), sum_re);
    // p.sub(c) ≡ sum_re
    F::axiom_eqv_transitive(t.mul(b).sub(u.mul(e)), p.sub(c), sum_re);
    // tb - ue ≡ sum_re

    // STEP 7: 0 ≤ t·β and t·β ≤ tb - ue
    // t·β = t·(b - e) = tb - te (by distributivity)
    // From u ≤ t and 0 ≤ e: ue ≤ te (mul_nonneg_monotone)
    // So tb - ue ≥ tb - te = t·β ≥ 0

    // 0 ≤ β (from 0 < β)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), beta);

    // 0 ≤ t·β (t ≥ 0, β ≥ 0)
    F::axiom_le_mul_nonneg_monotone(F::zero(), t, beta);
    // 0·β ≤ t·β
    ring_lemmas::lemma_mul_zero_left::<F>(beta);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().mul(beta), F::zero(), t.mul(beta)
    );
    // 0 ≤ t·β

    // u·e ≤ t·e: from u ≤ t, 0 ≤ e
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
    F::axiom_le_mul_nonneg_monotone(u, t, e);
    // u·e ≤ t·e

    // tb - ue ≥ tb - te: le_neg_flip on ue ≤ te → -te ≤ -ue, then add tb
    ordered_ring_lemmas::lemma_le_neg_flip::<F>(u.mul(e), t.mul(e));
    // -(t·e) ≤ -(u·e)
    F::axiom_le_add_monotone(t.mul(e).neg(), u.mul(e).neg(), t.mul(b));
    // (-te)+tb ≤ (-ue)+tb. Convert to sub form:
    // (-te)+tb ≡ tb+(-te) ≡ tb-te [comm + sub_is_add_neg]
    F::axiom_add_commutative(t.mul(e).neg(), t.mul(b));
    F::axiom_sub_is_add_neg(t.mul(b), t.mul(e));
    F::axiom_eqv_symmetric(t.mul(b).sub(t.mul(e)), t.mul(b).add(t.mul(e).neg()));
    F::axiom_eqv_transitive(
        t.mul(e).neg().add(t.mul(b)), t.mul(b).add(t.mul(e).neg()), t.mul(b).sub(t.mul(e))
    );
    // (-ue)+tb ≡ tb+(-ue) ≡ tb-ue
    F::axiom_add_commutative(u.mul(e).neg(), t.mul(b));
    F::axiom_sub_is_add_neg(t.mul(b), u.mul(e));
    F::axiom_eqv_symmetric(t.mul(b).sub(u.mul(e)), t.mul(b).add(u.mul(e).neg()));
    F::axiom_eqv_transitive(
        u.mul(e).neg().add(t.mul(b)), t.mul(b).add(u.mul(e).neg()), t.mul(b).sub(u.mul(e))
    );
    // Transfer le: tb-te ≤ tb-ue
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        t.mul(e).neg().add(t.mul(b)), t.mul(b).sub(t.mul(e)),
        u.mul(e).neg().add(t.mul(b))
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        t.mul(b).sub(t.mul(e)),
        u.mul(e).neg().add(t.mul(b)),
        t.mul(b).sub(u.mul(e))
    );
    // tb - te ≤ tb - ue

    // t·β ≡ tb - te: via distributivity
    // beta ≡ b.add(e.neg()) [axiom_sub_is_add_neg]
    F::axiom_sub_is_add_neg(b, e);
    ring_lemmas::lemma_mul_congruence_right::<F>(t, beta, b.add(e.neg()));
    // t·β ≡ t·(b+(-e))
    F::axiom_mul_distributes_left(t, b, e.neg());
    // t·(b+(-e)) ≡ tb + t·(-e)
    F::axiom_eqv_transitive(t.mul(beta), t.mul(b.add(e.neg())), t.mul(b).add(t.mul(e.neg())));
    // t·β ≡ tb + t·(-e)
    ring_lemmas::lemma_mul_neg_right::<F>(t, e);
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        t.mul(b), t.mul(e.neg()), t.mul(e).neg()
    );
    // tb + t·(-e) ≡ tb + (-te)
    F::axiom_eqv_transitive(t.mul(beta), t.mul(b).add(t.mul(e.neg())), t.mul(b).add(t.mul(e).neg()));
    // t·β ≡ tb + (-te) ≡ tb - te
    F::axiom_eqv_transitive(t.mul(beta), t.mul(b).add(t.mul(e).neg()), t.mul(b).sub(t.mul(e)));
    // t·β ≡ tb - te
    F::axiom_eqv_symmetric(t.mul(beta), t.mul(b).sub(t.mul(e)));
    // tb - te ≡ t·β

    // Chain: t·β ≤ tb - ue
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        t.mul(b).sub(t.mul(e)), t.mul(beta), t.mul(b).sub(u.mul(e))
    );

    // STEP 8: 0 ≤ t·β ≤ tb - ue, so (t·β)² ≤ (tb - ue)²
    ordered_ring_lemmas::lemma_square_le_square::<F>(t.mul(beta), t.mul(b).sub(u.mul(e)));

    // (tb-ue)² ≡ sum_re² (from step 6: tb-ue ≡ sum_re)
    F::axiom_eqv_reflexive(t.mul(b).sub(u.mul(e)));
    ring_lemmas::lemma_mul_congruence::<F>(
        t.mul(b).sub(u.mul(e)), sum_re,
        t.mul(b).sub(u.mul(e)), sum_re
    );
    // (tb-ue)² ≡ sum_re²

    // (t·β)² ≡ t²·β² by lemma_square_mul
    inequalities::lemma_square_mul::<F>(t, beta);
    // (t·β)·(t·β) ≡ t²·β²

    // STEP 9: d·β² ≤ t²·β² (from d ≤ t², β² ≥ 0)
    ordered_ring_lemmas::lemma_square_nonneg::<F>(beta);
    // 0 ≤ β²
    F::axiom_le_mul_nonneg_monotone(d, t.mul(t), beta.mul(beta));
    // d·β² ≤ t²·β²

    // STEP 10: Chain d·β² ≤ t²·β² ≤ (t·β)² ≤ (tb-ue)² ≡ sum_re²
    // t²·β² ≡ (t·β)² (symmetric of square_mul)
    F::axiom_eqv_symmetric(t.mul(beta).mul(t.mul(beta)), t.mul(t).mul(beta.mul(beta)));
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        d.mul(beta.mul(beta)), t.mul(t).mul(beta.mul(beta)), t.mul(beta).mul(t.mul(beta))
    );
    // d·β² ≤ (t·β)²

    F::axiom_le_transitive(d.mul(beta.mul(beta)), t.mul(beta).mul(t.mul(beta)),
        t.mul(b).sub(u.mul(e)).mul(t.mul(b).sub(u.mul(e))));
    // d·β² ≤ (tb-ue)²

    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        d.mul(beta.mul(beta)),
        t.mul(b).sub(u.mul(e)).mul(t.mul(b).sub(u.mul(e))),
        sum_re.mul(sum_re)
    );
    // d·β² ≤ sum_re²

    // STEP 11: β² ≡ (q+s)² (since β = -(q+s) and (-x)² = x²)
    ring_lemmas::lemma_neg_mul_neg::<F>(sum_im, sum_im);
    // sum_im.neg()·sum_im.neg() ≡ sum_im·sum_im, i.e., β² ≡ (q+s)²
    // Wait: β = b.sub(e) = q.neg().sub(s) and sum_im.neg() = (q+s).neg()
    // We showed earlier: sum_im.neg() ≡ β (from lemma_neg_add)
    // So β·β ≡ sum_im.neg()·sum_im.neg() by congruence
    F::axiom_eqv_reflexive(beta);
    ring_lemmas::lemma_mul_congruence::<F>(
        sum_im.neg(), beta, sum_im.neg(), beta
    );
    F::axiom_eqv_symmetric(sum_im.neg().mul(sum_im.neg()), beta.mul(beta));
    // β² ≡ (-sum_im)²

    // (-sum_im)² ≡ sum_im² by neg_mul_neg
    // β² ≡ sum_im²
    F::axiom_eqv_transitive(beta.mul(beta), sum_im.neg().mul(sum_im.neg()), sum_im.mul(sum_im));
    F::axiom_eqv_symmetric(beta.mul(beta), sum_im.mul(sum_im));
    // sum_im² ≡ β²

    // d·β² ≤ sum_re². Need d·sum_im² ≤ sum_re².
    // β² ≡ sum_im² (line 3019). Take symmetric for mul_congruence direction:
    // Already have sum_im² ≡ β² (line 3020). So d·β².eqv(d·sum_im²):
    F::axiom_eqv_reflexive(d);
    // β² ≡ sum_im² from eqv_transitive above
    F::axiom_eqv_symmetric(sum_im.mul(sum_im), beta.mul(beta));
    // β² ≡ sum_im²
    ring_lemmas::lemma_mul_congruence::<F>(d, d, beta.mul(beta), sum_im.mul(sum_im));
    // d·β² ≡ d·sum_im²
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        d.mul(beta.mul(beta)), d.mul(sum_im.mul(sum_im)), sum_re.mul(sum_re)
    );
    // d·sum_im² ≤ sum_re²

    // STEP 12: Conclude qe_nonneg for C2 case
    // sum_re ≥ 0 (given), sum_im < 0 (given), sum_im²d ≤ sum_re² (just proved)
    // Need: sum_im.mul(sum_im).mul(d).le(sum_re.mul(sum_re))
    // We proved: d.mul(sum_im.mul(sum_im)).le(sum_re.mul(sum_re))
    // These differ by commutativity of d and sum_im²
    F::axiom_mul_commutative(sum_im.mul(sum_im), d);
    // sum_im²·d ≡ d·sum_im²
    F::axiom_eqv_symmetric(sum_im.mul(sum_im).mul(d), d.mul(sum_im.mul(sum_im)));
    // d·sum_im² ≡ sum_im²·d
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        d.mul(sum_im.mul(sum_im)), sum_im.mul(sum_im).mul(d), sum_re.mul(sum_re)
    );
    // sum_im²·d ≤ sum_re² ✓
    // qe_nonneg C2 case: 0 ≤ sum_re, sum_im < 0, sum_im²·d ≤ sum_re²
}

/// Sub-case C of C2+C3: p+r < 0, q+s > 0, need (p+r)² ≤ (q+s)²d
proof fn lemma_nonneg_add_c2_c3_subC<F: OrderedField, R: PositiveRadicand<F>>(
    p: F, q: F, r: F, s: F,
)
    requires
        F::zero().le(p), q.lt(F::zero()), q.mul(q).mul(R::value()).le(p.mul(p)),
        r.lt(F::zero()), F::zero().lt(s), r.mul(r).le(s.mul(s).mul(R::value())),
        p.add(r).lt(F::zero()),
        F::zero().lt(q.add(s)),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(p.add(r), q.add(s))),
{
    let d = R::value();
    let sum_re = p.add(r);
    let sum_im = q.add(s);

    // STEP 0: Setup — b = -q > 0, e = s > 0, e > b (since q+s > 0)
    let b = q.neg();
    let e = s;

    // 0 < b (from q < 0)
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(q, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(b);
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero().neg(), F::zero(), b, b
    );
    // 0 < b

    // b ≢ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
    if b.eqv(F::zero()) { F::axiom_eqv_symmetric(b, F::zero()); }

    // STEP 1: c = -r > 0, u = c/e, show u ≥ 0 and u² ≤ d
    let c = r.neg();
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(r, F::zero());
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(c);
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(F::zero().neg(), F::zero(), c, c);
    // 0 < c

    // e ≢ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
    if e.eqv(F::zero()) { F::axiom_eqv_symmetric(e, F::zero()); }

    let u = c.div(e);

    // u ≥ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), c);
    ordered_field_lemmas::lemma_nonneg_div_pos::<F>(c, e);

    // u² ≤ d: from r² ≤ s²d, c² = r² (neg_mul_neg), e² = s²
    let e2 = e.mul(e);
    ring_lemmas::lemma_neg_mul_neg::<F>(r, r);
    // c² ≡ r². Need r² ≡ c² for le_congruence_left:
    F::axiom_eqv_symmetric(c.mul(c), r.mul(r));
    // r² ≡ c²
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        r.mul(r), c.mul(c), s.mul(s).mul(d)
    );
    // c² ≤ e²d

    // Swap to d·e² form, then divide
    F::axiom_mul_commutative(e2, d);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        c.mul(c), e2.mul(d), d.mul(e2)
    );
    // c² ≤ d·e²

    lemma_square_pos::<F>(e);
    ordered_field_lemmas::lemma_le_div_monotone::<F>(c.mul(c), d.mul(e2), e2);

    // c²/e² ≡ u²
    field_lemmas::lemma_div_mul_div::<F>(c, e, c, e);
    F::axiom_eqv_symmetric(u.mul(u), c.mul(c).div(e2));

    // d·e²/e² ≡ d
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), e2);
    if e2.eqv(F::zero()) { F::axiom_eqv_symmetric(e2, F::zero()); }
    field_lemmas::lemma_mul_div_cancel::<F>(d, e2);

    // u² ≤ d
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        c.mul(c).div(e2), u.mul(u), d.mul(e2).div(e2)
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        u.mul(u), d.mul(e2).div(e2), d
    );

    // STEP 2: t = p/b, show t ≥ 0 and d ≤ t²
    let t = p.div(b);
    ordered_field_lemmas::lemma_nonneg_div_pos::<F>(p, b);

    let b2 = b.mul(b);
    lemma_square_pos::<F>(b);
    ring_lemmas::lemma_neg_mul_neg::<F>(q, q);
    // b² ≡ q². Need q² ≡ b² for le_congruence_left(q²d, b²d, p²):
    F::axiom_eqv_symmetric(b.mul(b), q.mul(q));
    F::axiom_eqv_reflexive(d);
    ring_lemmas::lemma_mul_congruence::<F>(q.mul(q), b.mul(b), d, d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        q.mul(q).mul(d), b.mul(b).mul(d), p.mul(p)
    );
    // b²d ≤ p². Swap to d·b² form, then divide:
    F::axiom_mul_commutative(b2, d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        b2.mul(d), d.mul(b2), p.mul(p)
    );
    // d·b² ≤ p²
    ordered_field_lemmas::lemma_le_div_monotone::<F>(d.mul(b2), p.mul(p), b2);

    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b2);
    if b2.eqv(F::zero()) { F::axiom_eqv_symmetric(b2, F::zero()); }
    field_lemmas::lemma_mul_div_cancel::<F>(d, b2);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        d.mul(b2).div(b2), d, p.mul(p).div(b2)
    );
    field_lemmas::lemma_div_mul_div::<F>(p, b, p, b);
    F::axiom_eqv_symmetric(t.mul(t), p.mul(p).div(b2));
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(d, p.mul(p).div(b2), t.mul(t));
    // d ≤ t²

    // STEP 3: t ≥ u
    F::axiom_le_transitive(u.mul(u), d, t.mul(t));
    inequalities::lemma_square_le_implies_le::<F>(u, t);

    // STEP 4: γ = e - b > 0 (from q+s > 0, γ = s - (-q) = s + q = q+s = sum_im)
    let gamma = e.sub(b);  // γ = e - b

    // γ = e.sub(b). Bridge sub to add(neg):
    F::axiom_sub_is_add_neg(e, b);
    // gamma ≡ e.add(b.neg()) = s.add(q.neg().neg()) [since e=s, b=q.neg()]
    // q.neg().neg() ≡ q by neg_involution
    additive_group_lemmas::lemma_neg_involution::<F>(q);
    additive_group_lemmas::lemma_add_congruence_right::<F>(s, q.neg().neg(), q);
    // s.add(q.neg().neg()) ≡ s.add(q)
    // Chain: gamma ≡ s.add(b.neg()) = s.add(q.neg().neg()) ≡ s.add(q)
    F::axiom_eqv_transitive(gamma, s.add(b.neg()), s.add(q));
    F::axiom_add_commutative(s, q);
    F::axiom_eqv_transitive(gamma, s.add(q), sum_im);
    // γ ≡ sum_im

    // 0 < γ (from 0 < sum_im and γ ≡ sum_im)
    F::axiom_eqv_symmetric(gamma, sum_im);
    F::axiom_eqv_reflexive(F::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero(), F::zero(), sum_im, gamma
    );
    // 0 < γ
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), gamma);

    // STEP 5: tb ≡ p, ue ≡ c
    field_lemmas::lemma_div_mul_cancel::<F>(p, b);
    field_lemmas::lemma_div_mul_cancel::<F>(c, e);

    // STEP 6: ue - tb ≡ c - p ≡ -(p+r) = -sum_re > 0
    // ue - tb ≡ c - p (by sub_congruence)
    additive_group_lemmas::lemma_sub_congruence::<F>(u.mul(e), c, t.mul(b), p);
    // ue - tb ≡ c - p

    // STEP 7: ue - tb ≤ u·γ
    // ue - tb = ue - ub + ub - tb = u(e-b) + (u-t)b
    // Since u ≤ t and b > 0: ub ≤ tb, so -tb ≤ -ub, so ue - tb ≤ ue - ub = u·(e-b) = u·γ
    // i.e., just need: ue - tb ≤ u·γ

    // tb ≥ ub (from t ≥ u, 0 < b, by le_mul_nonneg_monotone)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
    F::axiom_le_mul_nonneg_monotone(u, t, b);
    // u·b ≤ t·b

    // -tb ≤ -ub
    ordered_ring_lemmas::lemma_le_neg_flip::<F>(u.mul(b), t.mul(b));

    // (-tb)+ue ≤ (-ub)+ue. Convert add terms to sub:
    F::axiom_le_add_monotone(t.mul(b).neg(), u.mul(b).neg(), u.mul(e));
    // (-tb)+ue ≡ ue+(-tb) ≡ ue-tb
    F::axiom_add_commutative(t.mul(b).neg(), u.mul(e));
    F::axiom_sub_is_add_neg(u.mul(e), t.mul(b));
    F::axiom_eqv_symmetric(u.mul(e).sub(t.mul(b)), u.mul(e).add(t.mul(b).neg()));
    F::axiom_eqv_transitive(
        t.mul(b).neg().add(u.mul(e)), u.mul(e).add(t.mul(b).neg()), u.mul(e).sub(t.mul(b))
    );
    // (-ub)+ue ≡ ue+(-ub) ≡ ue-ub
    F::axiom_add_commutative(u.mul(b).neg(), u.mul(e));
    F::axiom_sub_is_add_neg(u.mul(e), u.mul(b));
    F::axiom_eqv_symmetric(u.mul(e).sub(u.mul(b)), u.mul(e).add(u.mul(b).neg()));
    F::axiom_eqv_transitive(
        u.mul(b).neg().add(u.mul(e)), u.mul(e).add(u.mul(b).neg()), u.mul(e).sub(u.mul(b))
    );
    // Transfer le: ue-tb ≤ ue-ub
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        t.mul(b).neg().add(u.mul(e)), u.mul(e).sub(t.mul(b)),
        u.mul(b).neg().add(u.mul(e))
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        u.mul(e).sub(t.mul(b)),
        u.mul(b).neg().add(u.mul(e)),
        u.mul(e).sub(u.mul(b))
    );
    // ue - tb ≤ ue - ub

    // u·γ ≡ u·e - u·b: chain through u·(e + (-b))
    // gamma ≡ e.add(b.neg()) [axiom_sub_is_add_neg, already proved]
    ring_lemmas::lemma_mul_congruence_right::<F>(u, gamma, e.add(b.neg()));
    // u·γ ≡ u·(e + (-b))
    F::axiom_mul_distributes_left(u, e, b.neg());
    // u·(e+(-b)) ≡ u·e + u·(-b)
    F::axiom_eqv_transitive(u.mul(gamma), u.mul(e.add(b.neg())), u.mul(e).add(u.mul(b.neg())));
    // u·γ ≡ u·e + u·(-b)
    // u·(-b) ≡ -(u·b)
    ring_lemmas::lemma_mul_neg_right::<F>(u, b);
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        u.mul(e), u.mul(b.neg()), u.mul(b).neg()
    );
    // u·e + u·(-b) ≡ u·e + -(u·b)
    F::axiom_eqv_transitive(u.mul(gamma), u.mul(e).add(u.mul(b.neg())), u.mul(e).add(u.mul(b).neg()));
    // u·γ ≡ u·e + -(u·b)
    // u·e + -(u·b) ≡ u·e - u·b [symmetric of axiom_sub_is_add_neg]
    F::axiom_sub_is_add_neg(u.mul(e), u.mul(b));
    F::axiom_eqv_symmetric(u.mul(e).sub(u.mul(b)), u.mul(e).add(u.mul(b).neg()));
    F::axiom_eqv_transitive(u.mul(gamma), u.mul(e).add(u.mul(b).neg()), u.mul(e).sub(u.mul(b)));
    // u·γ ≡ u·e - u·b
    F::axiom_eqv_symmetric(u.mul(gamma), u.mul(e).sub(u.mul(b)));
    // u·e - u·b ≡ u·γ

    // ue - tb ≤ u·γ
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        u.mul(e).sub(t.mul(b)), u.mul(e).sub(u.mul(b)), u.mul(gamma)
    );

    // 0 ≤ u·γ (u ≥ 0, γ ≥ 0)
    F::axiom_le_mul_nonneg_monotone(F::zero(), u, gamma);
    ring_lemmas::lemma_mul_zero_left::<F>(gamma);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().mul(gamma), F::zero(), u.mul(gamma)
    );

    // 0 ≤ ue - tb: need to show this
    // We know ue ≡ c > 0 and tb ≡ p ≥ 0, but ue - tb ≡ c - p = -sum_re > 0
    // Actually we need: 0 ≤ ue - tb
    // sum_re < 0 → -sum_re > 0 → c - p > 0 (since c - p ≡ -(p+r) = -sum_re)
    // c - p = r.neg() - p = r.neg().add(p.neg()) = (r+p).neg()... hmm
    // Actually c - p = c.sub(p) = c.add(p.neg())
    // We have ue - tb ≡ c - p (proved above).
    // And sum_re = p + r, sum_re < 0, so -(p+r) > 0
    // c - p = (-r) - p = (-r) + (-p) = -(r + p) = -(p + r) [by commutativity] = -sum_re
    // So c - p > 0, meaning ue - tb > 0, hence 0 ≤ ue - tb
    // Let me prove: 0 < c - p
    // -sum_re > 0:
    ordered_ring_lemmas::lemma_lt_neg_flip::<F>(sum_re, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    F::axiom_eqv_reflexive(sum_re.neg());
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero().neg(), F::zero(), sum_re.neg(), sum_re.neg()
    );
    // 0 < -sum_re

    // -sum_re ≡ c - p: -(p+r) = (-p) + (-r) = (-p) + c
    additive_group_lemmas::lemma_neg_add::<F>(p, r);
    // -(p+r) ≡ (-p) + (-r) = p.neg().add(r.neg()) = p.neg().add(c)
    F::axiom_add_commutative(p.neg(), c);
    // p.neg().add(c) ≡ c.add(p.neg())
    F::axiom_eqv_transitive(sum_re.neg(), p.neg().add(c), c.add(p.neg()));
    // -sum_re ≡ c.add(p.neg())
    // c.add(p.neg()) ≡ c.sub(p) [symmetric of axiom_sub_is_add_neg]
    F::axiom_sub_is_add_neg(c, p);
    F::axiom_eqv_symmetric(c.sub(p), c.add(p.neg()));
    F::axiom_eqv_transitive(sum_re.neg(), c.add(p.neg()), c.sub(p));
    // -sum_re ≡ c - p

    // 0 < c - p
    F::axiom_eqv_reflexive(F::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero(), F::zero(), sum_re.neg(), c.sub(p)
    );
    // 0 < c - p

    // 0 < ue - tb (via congruence with ue - tb ≡ c - p)
    F::axiom_eqv_symmetric(u.mul(e).sub(t.mul(b)), c.sub(p));
    ordered_ring_lemmas::lemma_lt_congruence_both::<F>(
        F::zero(), F::zero(), c.sub(p), u.mul(e).sub(t.mul(b))
    );
    // 0 < ue - tb
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), u.mul(e).sub(t.mul(b)));
    // 0 ≤ ue - tb

    // STEP 8: (ue - tb)² ≤ (u·γ)² (since 0 ≤ ue-tb ≤ u·γ)
    ordered_ring_lemmas::lemma_square_le_square::<F>(
        u.mul(e).sub(t.mul(b)), u.mul(gamma)
    );

    // (u·γ)² ≡ u²·γ²
    inequalities::lemma_square_mul::<F>(u, gamma);

    // u²·γ² ≤ d·γ² (from u² ≤ d, γ² ≥ 0)
    ordered_ring_lemmas::lemma_square_nonneg::<F>(gamma);
    F::axiom_le_mul_nonneg_monotone(u.mul(u), d, gamma.mul(gamma));

    // Chain: (ue-tb)² ≤ (u·γ)² ≡ u²·γ² ≤ d·γ²
    // square_mul gives (u·γ)² ≡ u²·γ²
    // Use le_congruence_right to go from (ue-tb)² ≤ (u·γ)² to (ue-tb)² ≤ u²·γ²
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        u.mul(e).sub(t.mul(b)).mul(u.mul(e).sub(t.mul(b))),
        u.mul(gamma).mul(u.mul(gamma)),
        u.mul(u).mul(gamma.mul(gamma))
    );
    // (ue-tb)² ≤ u²·γ²
    F::axiom_le_transitive(
        u.mul(e).sub(t.mul(b)).mul(u.mul(e).sub(t.mul(b))),
        u.mul(u).mul(gamma.mul(gamma)),
        d.mul(gamma.mul(gamma))
    );
    // (ue-tb)² ≤ d·γ²

    // STEP 9: (ue-tb)² ≡ (tb-ue)² ≡ sum_re²
    // (-x)² = x²
    ring_lemmas::lemma_neg_mul_neg::<F>(
        t.mul(b).sub(u.mul(e)), t.mul(b).sub(u.mul(e))
    );
    // (tb-ue).neg()·(tb-ue).neg() ≡ (tb-ue)·(tb-ue)
    // But (tb-ue).neg() = ue - tb? Not directly: a.sub(b).neg() ≡ b.sub(a)?
    // Actually we need: (ue - tb) = (tb - ue).neg()
    // a.sub(b).neg() ≡ b.sub(a) is a standard identity:
    // a - b = a + (-b). -(a + (-b)) = (-a) + b [by neg_add] = b + (-a) = b - a
    // So (tb - ue).neg() ≡ ue - tb
    additive_group_lemmas::lemma_neg_add::<F>(t.mul(b), u.mul(e).neg());
    // (tb + (-ue)).neg() ≡ tb.neg() + (-ue).neg() = tb.neg() + ue
    additive_group_lemmas::lemma_neg_involution::<F>(u.mul(e));
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        t.mul(b).neg(), u.mul(e).neg().neg(), u.mul(e)
    );
    // tb.neg() + ue ≡ tb.neg().add(ue)... wait this is getting complicated.
    // Let me just use: (ue-tb)² = (ue-tb)·(ue-tb).
    // And: ue - tb ≡ c - p ≡ -sum_re (proved above).
    // So (ue-tb)² ≡ (-sum_re)² ≡ sum_re² by neg_mul_neg.
    // Easier chain!
    // Need: ue-tb ≡ -sum_re. We proved ue-tb ≡ c-p and -sum_re ≡ c-p.
    // So ue-tb ≡ c-p and c-p ≡ -sum_re (symmetric of -sum_re ≡ c-p)
    F::axiom_eqv_symmetric(sum_re.neg(), c.sub(p));
    F::axiom_eqv_transitive(u.mul(e).sub(t.mul(b)), c.sub(p), sum_re.neg());
    // ue-tb ≡ -sum_re

    // (ue-tb)² ≡ (-sum_re)²
    ring_lemmas::lemma_mul_congruence::<F>(
        u.mul(e).sub(t.mul(b)), sum_re.neg(),
        u.mul(e).sub(t.mul(b)), sum_re.neg()
    );

    // (-sum_re)² ≡ sum_re²
    ring_lemmas::lemma_neg_mul_neg::<F>(sum_re, sum_re);

    // (ue-tb)² ≡ sum_re²
    F::axiom_eqv_transitive(
        u.mul(e).sub(t.mul(b)).mul(u.mul(e).sub(t.mul(b))),
        sum_re.neg().mul(sum_re.neg()),
        sum_re.mul(sum_re)
    );

    // sum_re² ≤ d·γ² (from (ue-tb)² ≤ d·γ² and (ue-tb)² ≡ sum_re²)
    F::axiom_eqv_symmetric(
        u.mul(e).sub(t.mul(b)).mul(u.mul(e).sub(t.mul(b))),
        sum_re.mul(sum_re)
    );
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        u.mul(e).sub(t.mul(b)).mul(u.mul(e).sub(t.mul(b))),
        sum_re.mul(sum_re),
        d.mul(gamma.mul(gamma))
    );
    // sum_re² ≤ d·γ²

    // STEP 10: γ² ≡ sum_im² (since γ ≡ sum_im)
    ring_lemmas::lemma_mul_congruence::<F>(gamma, sum_im, gamma, sum_im);
    // γ² ≡ sum_im²

    // d·γ² ≡ d·sum_im²
    F::axiom_eqv_reflexive(d);
    ring_lemmas::lemma_mul_congruence::<F>(d, d, gamma.mul(gamma), sum_im.mul(sum_im));

    // sum_re² ≤ d·sum_im²
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        sum_re.mul(sum_re),
        d.mul(gamma.mul(gamma)),
        d.mul(sum_im.mul(sum_im))
    );

    // Need: sum_re² ≤ sum_im²·d (with mul order swapped)
    F::axiom_mul_commutative(sum_im.mul(sum_im), d);
    // sum_im²·d ≡ d·sum_im²
    F::axiom_eqv_symmetric(sum_im.mul(sum_im).mul(d), d.mul(sum_im.mul(sum_im)));
    // d·sum_im² ≡ sum_im²·d
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        sum_re.mul(sum_re),
        d.mul(sum_im.mul(sum_im)),
        sum_im.mul(sum_im).mul(d)
    );
    // sum_re² ≤ sum_im²·d ✓

    // qe_nonneg C3 case: sum_re < 0, 0 < sum_im, sum_re² ≤ sum_im²·d
}

/// Main lemma: nonneg is closed under addition.
pub proof fn lemma_nonneg_add_closed<F: OrderedField, R: PositiveRadicand<F>>(
    u: SpecQuadExt<F, R>,
    v: SpecQuadExt<F, R>,
)
    requires
        qe_nonneg::<F, R>(u),
        qe_nonneg::<F, R>(v),
    ensures
        qe_nonneg::<F, R>(qext::<F, R>(u.re.add(v.re), u.im.add(v.im))),
{
    let p = u.re;
    let q = u.im;
    let r = v.re;
    let s = v.im;
    let d = R::value();

    // Determine which case u and v satisfy
    let u_c1 = F::zero().le(p) && F::zero().le(q);
    let u_c2 = F::zero().le(p) && q.lt(F::zero()) && q.mul(q).mul(d).le(p.mul(p));
    let u_c3 = p.lt(F::zero()) && F::zero().lt(q) && p.mul(p).le(q.mul(q).mul(d));
    let v_c1 = F::zero().le(r) && F::zero().le(s);
    let v_c2 = F::zero().le(r) && s.lt(F::zero()) && s.mul(s).mul(d).le(r.mul(r));
    let v_c3 = r.lt(F::zero()) && F::zero().lt(s) && r.mul(r).le(s.mul(s).mul(d));

    if u_c1 && v_c1 {
        // C1+C1: trivial
        inequalities::lemma_nonneg_add::<F>(p, r);
        inequalities::lemma_nonneg_add::<F>(q, s);
    } else if u_c1 && v_c2 {
        lemma_nonneg_add_c1_c2::<F, R>(p, q, r, s);
    } else if u_c2 && v_c1 {
        // C2+C1 = C1+C2 with swapped args, then commute
        lemma_nonneg_add_c1_c2::<F, R>(r, s, p, q);
        // nonneg(r+p, s+q) → nonneg(p+r, q+s) by add commutativity
        F::axiom_add_commutative(r, p);
        F::axiom_add_commutative(s, q);
        lemma_nonneg_congruence::<F, R>(
            qext::<F, R>(r.add(p), s.add(q)),
            qext::<F, R>(p.add(r), q.add(s))
        );
    } else if u_c1 && v_c3 {
        lemma_nonneg_add_c1_c3::<F, R>(p, q, r, s);
    } else if u_c3 && v_c1 {
        // C3+C1 = C1+C3 with swapped args
        lemma_nonneg_add_c1_c3::<F, R>(r, s, p, q);
        F::axiom_add_commutative(r, p);
        F::axiom_add_commutative(s, q);
        lemma_nonneg_congruence::<F, R>(
            qext::<F, R>(r.add(p), s.add(q)),
            qext::<F, R>(p.add(r), q.add(s))
        );
    } else if u_c2 && v_c2 {
        lemma_nonneg_add_c2_c2::<F, R>(p, q, r, s);
    } else if u_c3 && v_c3 {
        lemma_nonneg_add_c3_c3::<F, R>(p, q, r, s);
    } else if u_c2 && v_c3 {
        lemma_nonneg_add_c2_c3::<F, R>(p, q, r, s);
    } else if u_c3 && v_c2 {
        // C3+C2 = C2+C3 with swapped args
        lemma_nonneg_add_c2_c3::<F, R>(r, s, p, q);
        F::axiom_add_commutative(r, p);
        F::axiom_add_commutative(s, q);
        lemma_nonneg_congruence::<F, R>(
            qext::<F, R>(r.add(p), s.add(q)),
            qext::<F, R>(p.add(r), q.add(s))
        );
    }
    // All 9 case combinations handled (u must be one of C1/C2/C3, v likewise)
}

/// Given a² ≥ b²d and c² ≥ e²d (with a,c,d ≥ 0), proves 0 ≤ a*c + b*e*d.
/// Key helper for nonneg_mul_closed: the "dominant product" in each component.
proof fn lemma_dominant_product<F: OrderedField>(
    a: F, b: F, c: F, e: F, d: F,
)
    requires
        b.mul(b).mul(d).le(a.mul(a)),  // b²d ≤ a²
        e.mul(e).mul(d).le(c.mul(c)),  // e²d ≤ c²
        F::zero().le(a),
        F::zero().le(c),
        F::zero().le(d),
    ensures
        F::zero().le(a.mul(c).add(b.mul(e).mul(d))),
{
    let ac = a.mul(c);
    let bed = b.mul(e).mul(d);

    // ac ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(a, c);

    if F::zero().le(bed) {
        // Both nonneg → sum nonneg
        lemma_nonneg_add::<F>(ac, bed);
    } else {
        // bed < 0. Show (bed)² ≤ (ac)², then bed.neg() ≤ ac, then ac + bed ≥ 0.

        // e²d ≥ 0
        ordered_ring_lemmas::lemma_square_nonneg::<F>(e);
        ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(e.mul(e), d);

        // a² ≥ 0
        ordered_ring_lemmas::lemma_square_nonneg::<F>(a);

        // Multiplication chain: b²d·e²d ≤ a²·e²d (step 1)
        F::axiom_le_mul_nonneg_monotone(b.mul(b).mul(d), a.mul(a), e.mul(e).mul(d));

        // e²d·a² ≤ c²·a² (step 2)
        F::axiom_le_mul_nonneg_monotone(e.mul(e).mul(d), c.mul(c), a.mul(a));

        // a²·e²d ≡ e²d·a² (commutativity)
        F::axiom_mul_commutative(a.mul(a), e.mul(e).mul(d));
        // b²d·e²d ≤ a²·e²d ≡ e²d·a² ≤ c²·a²
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            b.mul(b).mul(d).mul(e.mul(e).mul(d)),
            a.mul(a).mul(e.mul(e).mul(d)),
            e.mul(e).mul(d).mul(a.mul(a)),
        );
        F::axiom_le_transitive(
            b.mul(b).mul(d).mul(e.mul(e).mul(d)),
            e.mul(e).mul(d).mul(a.mul(a)),
            c.mul(c).mul(a.mul(a)),
        );
        // c²·a² ≡ a²·c²
        F::axiom_mul_commutative(c.mul(c), a.mul(a));
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            b.mul(b).mul(d).mul(e.mul(e).mul(d)),
            c.mul(c).mul(a.mul(a)),
            a.mul(a).mul(c.mul(c)),
        );
        // Now: b²d·e²d ≤ a²·c²

        // b²d·e²d ≡ (bed)² by lemma_sq_d_product
        lemma_sq_d_product::<F>(b, e, d);
        // a²·c² ≡ (ac)² by lemma_square_mul (reversed)
        lemma_square_mul::<F>(a, c);
        F::axiom_eqv_symmetric(ac.mul(ac), a.mul(a).mul(c.mul(c)));
        // Chain: (bed)² ≤ (ac)²
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            b.mul(b).mul(d).mul(e.mul(e).mul(d)),
            bed.mul(bed),
            a.mul(a).mul(c.mul(c)),
        );
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            bed.mul(bed),
            a.mul(a).mul(c.mul(c)),
            ac.mul(ac),
        );

        // (bed.neg())² ≡ (bed)² by neg_mul_neg
        ring_lemmas::lemma_neg_mul_neg::<F>(bed, bed);
        // neg_mul_neg: bed.neg()² ≡ bed². Symmetric: bed² ≡ bed.neg()²
        F::axiom_eqv_symmetric(bed.neg().mul(bed.neg()), bed.mul(bed));
        // bed² ≤ ac² and bed² ≡ bed.neg()² → bed.neg()² ≤ ac²
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            bed.mul(bed), bed.neg().mul(bed.neg()), ac.mul(ac),
        );

        // bed.neg() ≥ 0 (since bed ≤ 0)
        F::axiom_le_total(F::zero(), bed);
        // ¬(0 ≤ bed), so bed ≤ 0
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(bed, F::zero());
        // 0.neg() ≤ bed.neg()
        additive_group_lemmas::lemma_neg_zero::<F>();
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), bed.neg(),
        );
        // 0 ≤ bed.neg()

        // square_le_implies_le: bed.neg() ≤ ac
        lemma_square_le_implies_le::<F>(bed.neg(), ac);

        // Convert: bed.neg() ≤ ac → 0 ≤ ac - bed.neg() ≡ ac + bed
        ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(bed.neg(), ac);
        // 0 ≤ ac.sub(bed.neg())
        // ac.sub(bed.neg()) ≡ ac.add(bed.neg().neg()) ≡ ac.add(bed)
        F::axiom_sub_is_add_neg(ac, bed.neg());
        additive_group_lemmas::lemma_neg_involution::<F>(bed);
        additive_group_lemmas::lemma_add_congruence_right::<F>(
            ac, bed.neg().neg(), bed,
        );
        F::axiom_eqv_transitive(
            ac.sub(bed.neg()),
            ac.add(bed.neg().neg()),
            ac.add(bed),
        );
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(),
            ac.sub(bed.neg()),
            ac.add(bed),
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Norm multiplicativity and nonneg × nonneg helpers
// ═══════════════════════════════════════════════════════════════════

/// (a·c)·(b·e) ≡ (a·e)·(b·c) — rearrange a 4-factor product.
proof fn lemma_four_commute<F: Field>(a: F, c: F, b: F, e: F)
    ensures
        a.mul(c).mul(b.mul(e)).eqv(a.mul(e).mul(b.mul(c))),
{
    // (ac)(be) → (a(be))·c
    lemma_mul_swap_last_two::<F>(a, c, b.mul(e));
    // a(be) → b(ae) by swap_first_two
    lemma_mul_swap_first_two::<F>(a, b, e);
    F::axiom_mul_congruence_left(a.mul(b.mul(e)), b.mul(a.mul(e)), c);
    // b(ae)·c → (bc)·(ae) by swap_last_two
    lemma_mul_swap_last_two::<F>(b, a.mul(e), c);
    // (bc)(ae) → (ae)(bc) by commut
    F::axiom_mul_commutative(b.mul(c), a.mul(e));
    // Chain: (ac)(be) ≡ a(be)·c ≡ b(ae)·c ≡ (bc)(ae) ≡ (ae)(bc)
    F::axiom_eqv_transitive(
        a.mul(c).mul(b.mul(e)),
        a.mul(b.mul(e)).mul(c),
        b.mul(a.mul(e)).mul(c),
    );
    F::axiom_eqv_transitive(
        a.mul(c).mul(b.mul(e)),
        b.mul(a.mul(e)).mul(c),
        b.mul(c).mul(a.mul(e)),
    );
    F::axiom_eqv_transitive(
        a.mul(c).mul(b.mul(e)),
        b.mul(c).mul(a.mul(e)),
        a.mul(e).mul(b.mul(c)),
    );
}

/// norm(x·y) ≡ norm(x) · norm(y) — the norm is multiplicative.
///
/// The identity: (ac+bed)² - (ae+bc)²d = (a²-b²d)(c²-e²d)
/// follows from cross-term cancellation (2·ac·bed = 2·ae·bc·d).
#[verifier::rlimit(30)]
proof fn lemma_norm_mul<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
)
    ensures
        qe_norm::<F, R>(qe_mul::<F, R>(x, y)).eqv(
            qe_norm::<F, R>(x).mul(qe_norm::<F, R>(y))
        ),
{
    let a = x.re; let b = x.im;
    let c = y.re; let e = y.im;
    let d = R::value();
    let z = qe_mul::<F, R>(x, y);
    // z.re = ac + bed, z.im = ae + bc
    let ac = a.mul(c);
    let bed = b.mul(e).mul(d);
    let ae = a.mul(e);
    let bc = b.mul(c);
    let two = F::one().add(F::one());

    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let c2 = c.mul(c);
    let e2 = e.mul(e);
    let b2d = b2.mul(d);
    let e2d = e2.mul(d);
    let nx = a2.sub(b2d);  // norm(x)
    let ny = c2.sub(e2d);  // norm(y)

    // ─── RHS: expand nx·ny ───
    // nx·ny = (a² - b²d)·ny ≡ a²·ny - b²d·ny
    ring_lemmas::lemma_sub_mul_right::<F>(a2, b2d, ny);
    // a²·ny = a²·(c² - e²d) ≡ a²c² - a²e²d
    ring_lemmas::lemma_mul_distributes_over_sub::<F>(a2, c2, e2d);
    // b²d·ny = b²d·(c² - e²d) ≡ b²d·c² - b²d·e²d
    ring_lemmas::lemma_mul_distributes_over_sub::<F>(b2d, c2, e2d);

    // So nx·ny ≡ (a²c² - a²e²d) - (b²d·c² - b²d·e²d)
    // Using sub_pairs: (P-Q) - (R-S) ≡ (P-R) + (S-Q)
    // But that's tricky. Instead, connect through the 4-term form directly.

    // ─── LHS: expand norm(z) ───
    // z.re² = (ac + bed)²
    ring_lemmas::lemma_square_expand::<F>(ac, bed);
    // z.re² ≡ (ac)² + two·(ac)(bed) + (bed)²

    // z.im²d = (ae + bc)²·d
    lemma_square_expand_mul::<F>(ae, bc, d);
    // z.im²d ≡ (ae)²d + two·(ae)(bc)·d + (bc)²d

    // ─── Cross-term equality ───
    // (ac)(bed) ≡ (ae)(bc)·d
    // First: (ac)(bed) = (ac)·((be)·d)
    // By assoc_rev on ac, be, d: (ac)·(be·d) ≡ ((ac)(be))·d
    lemma_mul_assoc_rev::<F>(a.mul(c), b.mul(e), d);
    // (ac)(be) ≡ (ae)(bc) by four_commute
    lemma_four_commute::<F>(a, c, b, e);
    // So ((ac)(be))·d ≡ ((ae)(bc))·d by congr_left
    F::axiom_mul_congruence_left(
        a.mul(c).mul(b.mul(e)),
        a.mul(e).mul(b.mul(c)),
        d,
    );
    // Chain: (ac)(bed) ≡ ((ac)(be))·d ≡ ((ae)(bc))·d
    F::axiom_eqv_transitive(
        ac.mul(bed),
        a.mul(c).mul(b.mul(e)).mul(d),
        a.mul(e).mul(b.mul(c)).mul(d),
    );
    // ((ae)(bc))·d ≡ (ae)·((bc)·d) by assoc
    F::axiom_mul_associative(ae, bc, d);
    // But we want (ae)·(bc)·d = ae.mul(bc).mul(d) which IS the flat form.
    // Actually (ae)(bc)·d = a.mul(e).mul(b.mul(c)).mul(d) and
    // the square_expand_mul cross term is two.mul(ae.mul(bc)).mul(d).
    // ae.mul(bc) = a.mul(e).mul(b.mul(c)) ← yes, same thing.
    // So cross_lhs = two.mul(ac.mul(bed)) and cross_rhs = two.mul(ae.mul(bc)).mul(d).

    // two · cross_lhs ≡ two · cross_rhs
    // cross_lhs = ac.mul(bed), and we showed: ac.mul(bed) ≡ ae.mul(bc).mul(d)
    ring_lemmas::lemma_mul_congruence_right::<F>(
        two, ac.mul(bed), ae.mul(bc).mul(d),
    );
    // cross ≡ two·((ae·bc)·d) (will bridge to cross_d after let bindings)
    // Associativity: cross_d = two.mul(ae.mul(bc)).mul(d) ≡ two.mul(ae.mul(bc).mul(d))
    F::axiom_mul_associative(two, ae.mul(bc), d);
    F::axiom_eqv_symmetric(
        two.mul(ae.mul(bc)).mul(d),
        two.mul(ae.mul(bc).mul(d)),
    );

    // ─── Subtract expansions, cross terms cancel ───
    // z.re² ≡ (ac)² + (two·cross + (bed)²) where cross = (ac)(bed)
    // z.im²d ≡ (ae)²d + (two·cross_d + (bc)²d) where cross_d = (ae)(bc)·d
    // And two·cross ≡ two·cross_d (proved above).
    //
    // norm(z) = z.re² - z.im²d
    //         ≡ ((ac)² + two·cross + (bed)²) - ((ae)²d + two·cross + (bc)²d)
    // By sub_pairs: (P + Q) - (R + Q') where Q ≡ Q':
    //   ≡ (P - R) + (Q - Q') + ...
    // Actually let me use a cleaner approach.

    // Let's denote:
    //   A = (ac)², B = (bed)², C = (ae)²d, D = (bc)²d
    //   cross = two·(ac)(bed) ≡ two·(ae)(bc)·d
    //
    // z.re² ≡ A + cross + B = (A + cross) + B
    // z.im²d ≡ C + cross + D = (C + cross) + D
    //
    // norm(z) = z.re² - z.im²d
    //         ≡ ((A+cross)+B) - ((C+cross)+D)
    //         ≡ ((A+cross) - (C+cross)) + (B - D)    [sub_pairs]
    //         ≡ (A - C) + (B - D)                     [cancel cross]

    let cross = two.mul(ac.mul(bed));
    let cross_d = two.mul(ae.mul(bc)).mul(d);
    let sq_ac = ac.mul(ac);
    let sq_bed = bed.mul(bed);
    let sq_ae_d = ae.mul(ae).mul(d);
    let sq_bc_d = bc.mul(bc).mul(d);

    // Bridge: cross ≡ cross_d
    // mul_congruence_right gave: cross ≡ two·((ae·bc)·d)
    // axiom_mul_associative + symmetric gave: two·((ae·bc)·d) ≡ cross_d (reversed)
    // Actually: symmetric gave two.mul(ae.mul(bc).mul(d)).eqv(cross_d)
    // Chain: cross ≡ two·((ae·bc)·d) ≡ cross_d
    F::axiom_eqv_transitive(cross, two.mul(ae.mul(bc).mul(d)), cross_d);

    // Substitute cross ≡ cross_d in z.im²d expansion
    // z.im²d ≡ sq_ae_d + cross_d + sq_bc_d
    // cross_d ≡ cross (symmetric of what we proved)
    F::axiom_eqv_symmetric(cross, cross_d);
    // So z.im²d ≡ sq_ae_d + cross + sq_bc_d
    F::axiom_eqv_reflexive(sq_ae_d);
    additive_group_lemmas::lemma_add_congruence::<F>(
        sq_ae_d, sq_ae_d, cross_d, cross,
    );
    // sq_ae_d + cross_d ≡ sq_ae_d + cross
    F::axiom_eqv_reflexive(sq_bc_d);
    additive_group_lemmas::lemma_add_congruence::<F>(
        sq_ae_d.add(cross_d), sq_ae_d.add(cross),
        sq_bc_d, sq_bc_d,
    );
    // z.im²d ≡ (sq_ae_d + cross) + sq_bc_d

    // Now subtract using sub_pairs:
    // ((sq_ac + cross) + sq_bed) - ((sq_ae_d + cross) + sq_bc_d)
    // ≡ ((sq_ac + cross) - (sq_ae_d + cross)) + (sq_bed - sq_bc_d)

    // First congruence: z.re² ≡ (sq_ac + cross) + sq_bed
    // z.re² is the spec expression. Let's assert these equivalences.

    // The sub_pairs application needs:
    // norm(z) = z.re².sub(z.im²d)
    // and z.re² ≡ (sq_ac + cross) + sq_bed [from square_expand]
    // and z.im²d ≡ (sq_ae_d + cross) + sq_bc_d [from square_expand_mul + cross subst]

    // Use sub congruence to replace:
    let zre_expanded = sq_ac.add(cross).add(sq_bed);
    let zim_expanded = sq_ae_d.add(cross).add(sq_bc_d);

    // z.re.mul(z.re) ≡ zre_expanded (from square_expand)
    // z.im.mul(z.im).mul(d) ≡ zim_expanded (from square_expand_mul + cross subst)

    // Now: norm(z) = z.re² - z.im²d ≡ zre_expanded - zim_expanded

    // sub_pairs: (p+q) - (r+s) ≡ (p-r) + (q-s)
    // where p = sq_ac + cross, q = sq_bed, r = sq_ae_d + cross, s = sq_bc_d
    determinant::lemma_sub_pairs::<F>(
        sq_ac.add(cross), sq_bed, sq_ae_d.add(cross), sq_bc_d,
    );
    // ≡ ((sq_ac+cross) - (sq_ae_d+cross)) + (sq_bed - sq_bc_d)

    // Cancel cross: (sq_ac+cross) - (sq_ae_d+cross)
    // sub_pairs again: (sq_ac + cross) - (sq_ae_d + cross) ≡ (sq_ac - sq_ae_d) + (cross - cross)
    determinant::lemma_sub_pairs::<F>(sq_ac, cross, sq_ae_d, cross);
    // cross - cross ≡ 0
    additive_group_lemmas::lemma_sub_self::<F>(cross);
    // (sq_ac - sq_ae_d) + 0 ≡ sq_ac - sq_ae_d
    F::axiom_add_zero_right(sq_ac.sub(sq_ae_d));
    // Chain: (sq_ac+cross) - (sq_ae_d+cross) ≡ (sq_ac - sq_ae_d) + 0 ≡ sq_ac - sq_ae_d
    F::axiom_eqv_reflexive(sq_ac.sub(sq_ae_d));
    additive_group_lemmas::lemma_add_congruence::<F>(
        sq_ac.sub(sq_ae_d), sq_ac.sub(sq_ae_d),
        cross.sub(cross), F::zero(),
    );
    F::axiom_eqv_transitive(
        sq_ac.add(cross).sub(sq_ae_d.add(cross)),
        sq_ac.sub(sq_ae_d).add(cross.sub(cross)),
        sq_ac.sub(sq_ae_d).add(F::zero()),
    );
    F::axiom_eqv_transitive(
        sq_ac.add(cross).sub(sq_ae_d.add(cross)),
        sq_ac.sub(sq_ae_d).add(F::zero()),
        sq_ac.sub(sq_ae_d),
    );

    // So norm(z) ≡ (sq_ac - sq_ae_d) + (sq_bed - sq_bc_d)
    F::axiom_eqv_reflexive(sq_bed.sub(sq_bc_d));
    additive_group_lemmas::lemma_add_congruence::<F>(
        sq_ac.add(cross).sub(sq_ae_d.add(cross)), sq_ac.sub(sq_ae_d),
        sq_bed.sub(sq_bc_d), sq_bed.sub(sq_bc_d),
    );
    // Chain: zre_expanded - zim_expanded ≡ ... ≡ (sq_ac - sq_ae_d) + (sq_bed - sq_bc_d)
    F::axiom_eqv_transitive(
        zre_expanded.sub(zim_expanded),
        sq_ac.add(cross).sub(sq_ae_d.add(cross)).add(sq_bed.sub(sq_bc_d)),
        sq_ac.sub(sq_ae_d).add(sq_bed.sub(sq_bc_d)),
    );

    // ─── Factor first pair: sq_ac - sq_ae_d ≡ a²·ny ───
    // (ac)² ≡ a²c² by square_mul
    lemma_square_mul::<F>(a, c);
    F::axiom_eqv_symmetric(ac.mul(ac), a2.mul(c2));
    // (ae)² ≡ a²e²
    lemma_square_mul::<F>(a, e);
    F::axiom_eqv_symmetric(ae.mul(ae), a2.mul(e2));
    // (ae)²·d ≡ a²e²·d
    F::axiom_mul_congruence_left(ae.mul(ae), a2.mul(e2), d);
    // a²e²·d ≡ a²·(e²d) by assoc
    F::axiom_mul_associative(a2, e2, d);
    // Chain: (ae)²d ≡ a²e²d ≡ a²·e²d
    F::axiom_eqv_transitive(ae.mul(ae).mul(d), a2.mul(e2).mul(d), a2.mul(e2d));

    // sq_ac - sq_ae_d = (ac)² - (ae)²d ≡ a²c² - a²·e²d
    additive_group_lemmas::lemma_sub_congruence::<F>(
        sq_ac, a2.mul(c2),
        sq_ae_d, a2.mul(e2d),
    );
    // a²c² - a²e²d ≡ a²·(c² - e²d) = a²·ny
    ring_lemmas::lemma_mul_distributes_over_sub::<F>(a2, c2, e2d);
    F::axiom_eqv_symmetric(a2.mul(ny), a2.mul(c2).sub(a2.mul(e2d)));
    // Chain:
    F::axiom_eqv_transitive(
        sq_ac.sub(sq_ae_d),
        a2.mul(c2).sub(a2.mul(e2d)),
        a2.mul(ny),
    );

    // ─── Factor second pair: sq_bed - sq_bc_d ≡ -(b²d·ny) ───
    // (bed)² ≡ b²d·e²d by sq_d_product
    lemma_sq_d_product::<F>(b, e, d);
    F::axiom_eqv_symmetric(b2d.mul(e2d), bed.mul(bed));

    // (bc)²·d: first (bc)² ≡ b²c²
    lemma_square_mul::<F>(b, c);
    F::axiom_eqv_symmetric(bc.mul(bc), b2.mul(c2));
    // (bc)²d ≡ b²c²·d
    F::axiom_mul_congruence_left(bc.mul(bc), b2.mul(c2), d);
    // b²c²·d ≡ b²·(c²d) by assoc
    F::axiom_mul_associative(b2, c2, d);
    F::axiom_eqv_transitive(bc.mul(bc).mul(d), b2.mul(c2).mul(d), b2.mul(c2.mul(d)));
    // b²·(c²d) ≡ b²·(d·c²) ≡ b²d·c² by commut + assoc
    F::axiom_mul_commutative(c2, d);
    ring_lemmas::lemma_mul_congruence_right::<F>(b2, c2.mul(d), d.mul(c2));
    lemma_mul_assoc_rev::<F>(b2, d, c2);
    F::axiom_eqv_transitive(b2.mul(c2.mul(d)), b2.mul(d.mul(c2)), b2.mul(d).mul(c2));
    // Chain: (bc)²d ≡ b²(c²d) ≡ b²(dc²) ≡ (b²d)c² = b2d·c2
    F::axiom_eqv_transitive(
        sq_bc_d, b2.mul(c2.mul(d)), b2.mul(d.mul(c2)),
    );
    F::axiom_eqv_transitive(sq_bc_d, b2.mul(d.mul(c2)), b2d.mul(c2));

    // sq_bed - sq_bc_d ≡ b²d·e²d - b²d·c²
    additive_group_lemmas::lemma_sub_congruence::<F>(
        sq_bed, b2d.mul(e2d),
        sq_bc_d, b2d.mul(c2),
    );
    // b²d·e²d - b²d·c² ≡ b²d·(e²d - c²) by mul_distributes_over_sub reversed
    ring_lemmas::lemma_mul_distributes_over_sub::<F>(b2d, e2d, c2);
    F::axiom_eqv_symmetric(b2d.mul(e2d.sub(c2)), b2d.mul(e2d).sub(b2d.mul(c2)));
    F::axiom_eqv_transitive(
        sq_bed.sub(sq_bc_d),
        b2d.mul(e2d).sub(b2d.mul(c2)),
        b2d.mul(e2d.sub(c2)),
    );
    // e²d - c² ≡ -(c² - e²d) = -(ny)
    additive_group_lemmas::lemma_sub_antisymmetric::<F>(e2d, c2);
    // e2d.sub(c2).eqv(c2.sub(e2d).neg()) = ny.neg()
    ring_lemmas::lemma_mul_congruence_right::<F>(b2d, e2d.sub(c2), ny.neg());
    // b²d·(-(ny)) ≡ -(b²d·ny)
    ring_lemmas::lemma_mul_neg_right::<F>(b2d, ny);
    F::axiom_eqv_transitive(
        b2d.mul(e2d.sub(c2)),
        b2d.mul(ny.neg()),
        b2d.mul(ny).neg(),
    );
    // Chain: sq_bed - sq_bc_d ≡ b²d·(e²d-c²) ≡ b²d·(-ny) ≡ -(b²d·ny)
    F::axiom_eqv_transitive(
        sq_bed.sub(sq_bc_d),
        b2d.mul(e2d.sub(c2)),
        b2d.mul(ny).neg(),
    );

    // ─── Combine: (sq_ac - sq_ae_d) + (sq_bed - sq_bc_d) ≡ a²·ny + (-(b²d·ny)) ───
    additive_group_lemmas::lemma_add_congruence::<F>(
        sq_ac.sub(sq_ae_d), a2.mul(ny),
        sq_bed.sub(sq_bc_d), b2d.mul(ny).neg(),
    );
    // a²·ny + (-(b²d·ny)) ≡ a²·ny - b²d·ny by sub_is_add_neg reversed
    F::axiom_sub_is_add_neg(a2.mul(ny), b2d.mul(ny));
    F::axiom_eqv_symmetric(a2.mul(ny).sub(b2d.mul(ny)), a2.mul(ny).add(b2d.mul(ny).neg()));
    F::axiom_eqv_transitive(
        sq_ac.sub(sq_ae_d).add(sq_bed.sub(sq_bc_d)),
        a2.mul(ny).add(b2d.mul(ny).neg()),
        a2.mul(ny).sub(b2d.mul(ny)),
    );
    // a²·ny - b²d·ny ≡ (a² - b²d)·ny = nx·ny by sub_mul_right reversed
    ring_lemmas::lemma_sub_mul_right::<F>(a2, b2d, ny);
    F::axiom_eqv_symmetric(nx.mul(ny), a2.mul(ny).sub(b2d.mul(ny)));
    F::axiom_eqv_transitive(
        sq_ac.sub(sq_ae_d).add(sq_bed.sub(sq_bc_d)),
        a2.mul(ny).sub(b2d.mul(ny)),
        nx.mul(ny),
    );

    // ─── Final chain: norm(z) ≡ LHS_expanded ≡ 4 terms ≡ nx·ny ───
    // norm(z) = z.re² - z.im²d
    // z.re² ≡ zre_expanded (from square_expand)
    // z.im²d ≡ zim_expanded (from square_expand_mul + cross subst)
    // norm(z) ≡ zre_expanded - zim_expanded by sub congruence
    // ≡ sub_pairs result ≡ (sq_ac-sq_ae_d) + (sq_bed-sq_bc_d) ≡ nx·ny

    // Step A: z.re.mul(z.re) ≡ zre_expanded
    // square_expand gave: ac.add(bed).mul(ac.add(bed)) ≡ sq_ac + cross + sq_bed

    // Step B: z.im.mul(z.im).mul(d) ≡ zim_expanded
    // square_expand_mul + cross subst (done above)
    // We need to chain: z.im.mul(z.im).mul(d) ≡ original_expansion ≡ zim_expanded
    // The original expansion from square_expand_mul is:
    //   ae.add(bc).mul(ae.add(bc)).mul(d) ≡ sq_ae_d + cross_d + sq_bc_d
    // Then we showed cross_d ≡ cross, giving:
    //   ≡ sq_ae_d + cross + sq_bc_d = zim_expanded
    let zim_orig = sq_ae_d.add(cross_d).add(sq_bc_d);
    F::axiom_eqv_transitive(
        ae.add(bc).mul(ae.add(bc)).mul(d),
        zim_orig,
        zim_expanded,
    );

    // Step C: norm(z) ≡ zre_expanded - zim_expanded by sub congruence
    additive_group_lemmas::lemma_sub_congruence::<F>(
        z.re.mul(z.re), zre_expanded,
        z.im.mul(z.im).mul(d), zim_expanded,
    );

    // Step D: zre_expanded - zim_expanded ≡ (sq_ac-sq_ae_d)+(sq_bed-sq_bc_d) by sub_pairs
    // (already proved above)

    // Step E: chain all
    F::axiom_eqv_transitive(
        z.re.mul(z.re).sub(z.im.mul(z.im).mul(d)),
        zre_expanded.sub(zim_expanded),
        sq_ac.sub(sq_ae_d).add(sq_bed.sub(sq_bc_d)),
    );
    F::axiom_eqv_transitive(
        z.re.mul(z.re).sub(z.im.mul(z.im).mul(d)),
        sq_ac.sub(sq_ae_d).add(sq_bed.sub(sq_bc_d)),
        nx.mul(ny),
    );
}

/// If P ≥ 0 and Q² ≤ P², then 0 ≤ P + Q.
proof fn lemma_square_dominance_sum<F: OrderedField>(p: F, q: F)
    requires
        F::zero().le(p),
        q.mul(q).le(p.mul(p)),
    ensures
        F::zero().le(p.add(q)),
{
    if F::zero().le(q) {
        lemma_nonneg_add::<F>(p, q);
    } else {
        // q < 0. Show -q ≤ p, so p + q ≥ 0.
        // -q ≥ 0
        F::axiom_le_total(F::zero(), q);
        // ¬(0 ≤ q), so q ≤ 0
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(q, F::zero());
        // 0.neg() ≤ q.neg()
        additive_group_lemmas::lemma_neg_zero::<F>();
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), q.neg(),
        );
        // 0 ≤ q.neg()

        // (-q)² ≡ q² by neg_mul_neg
        ring_lemmas::lemma_neg_mul_neg::<F>(q, q);
        // q.neg().mul(q.neg()).eqv(q.mul(q))
        // So q² ≤ p² becomes (-q)² ≤ p² by le_congruence_left
        F::axiom_eqv_symmetric(q.neg().mul(q.neg()), q.mul(q));
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            q.mul(q), q.neg().mul(q.neg()), p.mul(p),
        );
        // (-q)² ≤ p²

        // By square_le_implies_le: -q ≤ p
        lemma_square_le_implies_le::<F>(q.neg(), p);

        // -q ≤ p → 0 ≤ p - (-q)
        ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(q.neg(), p);
        // p - (-q) ≡ p + q
        F::axiom_sub_is_add_neg(p, q.neg());
        additive_group_lemmas::lemma_neg_involution::<F>(q);
        additive_group_lemmas::lemma_add_congruence_right::<F>(
            p, q.neg().neg(), q,
        );
        F::axiom_eqv_transitive(
            p.sub(q.neg()),
            p.add(q.neg().neg()),
            p.add(q),
        );
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(),
            p.sub(q.neg()),
            p.add(q),
        );
    }
}

/// a ≤ b implies a - b ≤ 0.
proof fn lemma_sub_nonpos<F: OrderedField>(a: F, b: F)
    requires a.le(b),
    ensures a.sub(b).le(F::zero()),
{
    F::axiom_le_add_monotone(a, b, b.neg());
    F::axiom_sub_is_add_neg(a, b);
    F::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        a.add(b.neg()), a.sub(b), b.add(b.neg()),
    );
    F::axiom_add_inverse_right(b);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        a.sub(b), b.add(b.neg()), F::zero(),
    );
}

/// a - b ≤ 0 implies a ≤ b. (Converse of lemma_sub_nonpos.)
proof fn lemma_nonpos_sub_implies_le<F: OrderedField>(a: F, b: F)
    requires a.sub(b).le(F::zero()),
    ensures a.le(b),
{
    F::axiom_le_add_monotone(a.sub(b), F::zero(), b);
    additive_group_lemmas::lemma_sub_then_add_cancel::<F>(a, b);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        a.sub(b).add(b), a, F::zero().add(b),
    );
    additive_group_lemmas::lemma_add_zero_left::<F>(b);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        a, F::zero().add(b), b,
    );
}

/// z.re ≥ 0 and norm(z) ≥ 0 implies nonneg(z).
///
/// If z.im ≥ 0: C1. If z.im < 0: C2 (z.im²d ≤ z.re² from norm ≥ 0).
proof fn lemma_nonneg_conclude_re<F: OrderedField, R: PositiveRadicand<F>>(
    z: SpecQuadExt<F, R>,
)
    requires
        F::zero().le(z.re),
        F::zero().le(qe_norm::<F, R>(z)),
    ensures
        qe_nonneg::<F, R>(z),
{
    let d = R::value();
    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
    F::axiom_le_total(F::zero(), z.im);
    if F::zero().le(z.im) {
        // C1: z.re ≥ 0, z.im ≥ 0
    } else {
        // C2: z.re ≥ 0, z.im < 0, need z.im²d ≤ z.re²
        // Prove z.im.lt(0): z.im.le(0) from le_total, and !z.im.eqv(0) by contradiction
        if z.im.eqv(F::zero()) {
            F::axiom_eqv_symmetric(z.im, F::zero());
            F::axiom_le_total(F::zero(), F::zero());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(F::zero(), F::zero(), z.im);
            assert(false); // contradicts !0.le(z.im)
        }
        F::axiom_lt_iff_le_and_not_eqv(z.im, F::zero());
        // norm ≥ 0: 0 ≤ z.re² - z.im²d
        // Derive z.im²d ≤ z.re² using add_monotone
        let b2d_r = z.im.mul(z.im).mul(d);
        let a2_r = z.re.mul(z.re);
        F::axiom_le_add_monotone(F::zero(), a2_r.sub(b2d_r), b2d_r);
        additive_group_lemmas::lemma_add_zero_left::<F>(b2d_r);
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().add(b2d_r), b2d_r, a2_r.sub(b2d_r).add(b2d_r),
        );
        additive_group_lemmas::lemma_sub_then_add_cancel::<F>(a2_r, b2d_r);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            b2d_r, a2_r.sub(b2d_r).add(b2d_r), a2_r,
        );
    }
}

/// z.im ≥ 0 and norm(z) ≤ 0 implies nonneg(z).
///
/// If z.re ≥ 0: C1. If z.re < 0: show z.im > 0 (from z.im ≡ 0 → z.re ≡ 0 contradiction), then C3.
#[verifier::rlimit(30)]
proof fn lemma_nonneg_conclude_im<F: OrderedField, R: PositiveRadicand<F>>(
    z: SpecQuadExt<F, R>,
)
    requires
        F::zero().le(z.im),
        qe_norm::<F, R>(z).le(F::zero()),
    ensures
        qe_nonneg::<F, R>(z),
{
    let d = R::value();
    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
    F::axiom_le_total(F::zero(), z.re);
    if F::zero().le(z.re) {
        // C1: z.re ≥ 0, z.im ≥ 0
    } else {
        // z.re < 0. Need C3: z.re < 0, z.im > 0, z.re² ≤ z.im²d.

        // Derive z.re² ≤ z.im²d from norm ≤ 0 using add_monotone
        let b2d_i = z.im.mul(z.im).mul(d);
        let a2_i = z.re.mul(z.re);
        // norm = a2_i - b2d_i ≤ 0, add b2d_i to both sides
        F::axiom_le_add_monotone(a2_i.sub(b2d_i), F::zero(), b2d_i);
        additive_group_lemmas::lemma_sub_then_add_cancel::<F>(a2_i, b2d_i);
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            a2_i.sub(b2d_i).add(b2d_i), a2_i, F::zero().add(b2d_i),
        );
        additive_group_lemmas::lemma_add_zero_left::<F>(b2d_i);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            a2_i, F::zero().add(b2d_i), b2d_i,
        );
        // z.re² ≤ z.im²d ✓

        // Derive z.re.lt(0): z.re.le(0) from le_total, and !z.re.eqv(0) by contradiction
        if z.re.eqv(F::zero()) {
            F::axiom_eqv_symmetric(z.re, F::zero());
            F::axiom_le_total(F::zero(), F::zero());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(F::zero(), F::zero(), z.re);
            assert(false); // contradicts !0.le(z.re)
        }
        F::axiom_lt_iff_le_and_not_eqv(z.re, F::zero());

        // Derive z.im > 0 (strictly). If z.im ≡ 0: z.im²d ≡ 0, z.re² ≤ 0 ∧ z.re² ≥ 0 → z.re² ≡ 0.
        // Field: z.re² ≡ 0 ∧ z.re ≢ 0 → contradiction (multiply by z.re.recip()).
        if z.im.eqv(F::zero()) {
            // z.im² ≡ 0
            F::axiom_eqv_symmetric(z.im, F::zero());
            F::axiom_mul_congruence_left(F::zero(), z.im, z.im);
            ring_lemmas::lemma_mul_zero_left::<F>(z.im);
            F::axiom_eqv_symmetric(F::zero().mul(z.im), z.im.mul(z.im));
            F::axiom_eqv_transitive(z.im.mul(z.im), F::zero().mul(z.im), F::zero());
            // z.im²d ≡ 0
            F::axiom_mul_congruence_left(z.im.mul(z.im), F::zero(), d);
            ring_lemmas::lemma_mul_zero_left::<F>(d);
            F::axiom_eqv_transitive(b2d_i, F::zero().mul(d), F::zero());
            // z.re² ≤ z.im²d ≡ 0 → z.re² ≤ 0
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(a2_i, b2d_i, F::zero());
            // z.re² ≥ 0
            ordered_ring_lemmas::lemma_square_nonneg::<F>(z.re);
            // z.re² ≡ 0
            F::axiom_le_antisymmetric(a2_i, F::zero());
            // Field inverse: z.re.recip() * z.re² ≡ z.re.recip() * 0 ≡ 0
            ring_lemmas::lemma_mul_congruence_right::<F>(z.re.recip(), a2_i, F::zero());
            F::axiom_mul_commutative(z.re.recip(), F::zero());
            ring_lemmas::lemma_mul_zero_left::<F>(z.re.recip());
            F::axiom_eqv_transitive(
                z.re.recip().mul(F::zero()), F::zero().mul(z.re.recip()), F::zero(),
            );
            F::axiom_eqv_transitive(
                z.re.recip().mul(a2_i), z.re.recip().mul(F::zero()), F::zero(),
            );
            // z.re.recip() * z.re² ≡ (z.re.recip() * z.re) * z.re ≡ 1 * z.re ≡ z.re
            lemma_mul_assoc_rev::<F>(z.re.recip(), z.re, z.re);
            field_lemmas::lemma_mul_recip_left::<F>(z.re);
            F::axiom_mul_congruence_left(z.re.recip().mul(z.re), F::one(), z.re);
            ring_lemmas::lemma_mul_one_left::<F>(z.re);
            F::axiom_eqv_transitive(
                z.re.recip().mul(z.re).mul(z.re), F::one().mul(z.re), z.re,
            );
            F::axiom_eqv_transitive(
                z.re.recip().mul(a2_i), z.re.recip().mul(z.re).mul(z.re), z.re,
            );
            // z.re ≡ 0 (from z.re.recip()*z.re² ≡ 0 and ≡ z.re)
            F::axiom_eqv_symmetric(z.re.recip().mul(a2_i), z.re);
            F::axiom_eqv_transitive(z.re, z.re.recip().mul(a2_i), F::zero());
            // But z.re ≢ 0 from the earlier block → contradiction
            assert(false);
        }
        // z.im ≢ 0 combined with 0.le(z.im) [requires] → 0.lt(z.im)
        // Z3 needs !0.eqv(z.im), but if-block above gave !z.im.eqv(0). Bridge via symmetric:
        F::axiom_eqv_symmetric(F::zero(), z.im);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), z.im);
        // z.re.lt(0) ✓, 0.lt(z.im) ✓, z.re² ≤ z.im²d ✓ → C3
    }
}

/// Cross dominance: 0≤a, 0≤e, 0≤d, b²d≤a², c²≤e²d → 0≤ae+bc.
///
/// The dominant term ae ≥ 0, and (bc)² ≤ (ae)² from the multiplication chain.
#[verifier::rlimit(20)]
proof fn lemma_cross_dominance<F: OrderedField>(
    a: F, b: F, c: F, e: F, d: F,
)
    requires
        F::zero().le(a),
        F::zero().le(e),
        F::zero().le(d),
        b.mul(b).mul(d).le(a.mul(a)),
        c.mul(c).le(e.mul(e).mul(d)),
    ensures
        F::zero().le(a.mul(e).add(b.mul(c))),
{
    // ae ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(a, e);
    // Need (bc)² ≤ (ae)²
    // (bc)² = b²c². (ae)² = a²e².
    // From c² ≤ e²d, multiply by b² ≥ 0: b²c² ≤ b²·(e²d)
    ordered_ring_lemmas::lemma_square_nonneg::<F>(b);
    F::axiom_le_mul_nonneg_monotone(c.mul(c), e.mul(e).mul(d), b.mul(b));
    // c²·b² ≤ (e²d)·b²
    // c²·b² ≡ (bc)² by square_mul (reversed)
    lemma_square_mul::<F>(b, c);
    F::axiom_eqv_symmetric(b.mul(c).mul(b.mul(c)), b.mul(b).mul(c.mul(c)));
    // b²c² ≡ (bc)²
    F::axiom_mul_commutative(c.mul(c), b.mul(b));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        c.mul(c).mul(b.mul(b)), b.mul(b).mul(c.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b)),
    );
    F::axiom_eqv_symmetric(b.mul(c).mul(b.mul(c)), b.mul(b).mul(c.mul(c)));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        b.mul(b).mul(c.mul(c)), b.mul(c).mul(b.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b)),
    );
    // (bc)² ≤ (e²d)·b²
    // (e²d)·b² = e²·d·b² = (b²d)·e² by commuting
    // From b²d ≤ a², multiply by e² ≥ 0: (b²d)·e² ≤ a²·e²
    ordered_ring_lemmas::lemma_square_nonneg::<F>(e);
    F::axiom_le_mul_nonneg_monotone(b.mul(b).mul(d), a.mul(a), e.mul(e));
    // (b²d)·e² ≤ a²·e²
    // a²·e² ≡ (ae)² by square_mul (reversed)
    lemma_square_mul::<F>(a, e);
    F::axiom_eqv_symmetric(a.mul(e).mul(a.mul(e)), a.mul(a).mul(e.mul(e)));
    // a²e² ≡ (ae)²
    // Need to chain: (e²d)·b² ≡ (b²d)·e²
    // e²d·b² = (e²·d)·b². b²d·e² = (b²·d)·e².
    // (e²·d)·b² = e²·(d·b²) by assoc. d·b² = b²·d by commut. So e²·b²d.
    // (b²·d)·e² = b²d·e². And e²·b²d = e²·(b²d). Commute: b²d·e² ≡ e²·b²d? By commut.
    F::axiom_mul_commutative(e.mul(e).mul(d), b.mul(b));
    // (e²d)·b² ≡ b²·(e²d) = b.mul(b).mul(e.mul(e).mul(d))
    // And b²·(e²d): need this ≡ (b²d)·e² = b.mul(b).mul(d).mul(e.mul(e))
    // b²·(e²d) = b²·(e²·d). (b²d)·e² = (b²·d)·e².
    // b²·(e²·d) ≡ b²·(d·e²) by commut inside, then ≡ (b²·d)·e² by assoc_rev.
    F::axiom_mul_commutative(e.mul(e), d);
    ring_lemmas::lemma_mul_congruence_right::<F>(b.mul(b), e.mul(e).mul(d), d.mul(e.mul(e)));
    lemma_mul_assoc_rev::<F>(b.mul(b), d, e.mul(e));
    F::axiom_eqv_transitive(
        b.mul(b).mul(e.mul(e).mul(d)),
        b.mul(b).mul(d.mul(e.mul(e))),
        b.mul(b).mul(d).mul(e.mul(e)),
    );
    // Chain: (e²d)·b² ≡ b²·(e²d) ≡ (b²d)·e²
    F::axiom_eqv_transitive(
        e.mul(e).mul(d).mul(b.mul(b)),
        b.mul(b).mul(e.mul(e).mul(d)),
        b.mul(b).mul(d).mul(e.mul(e)),
    );
    // (bc)² ≤ (e²d)·b² and (e²d)·b² ≡ (b²d)·e², so (bc)² ≤ (b²d)·e²
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        b.mul(c).mul(b.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b)),
        b.mul(b).mul(d).mul(e.mul(e)),
    );
    // (b²d)·e² ≤ a²·e² from axiom_le_mul_nonneg_monotone
    F::axiom_le_transitive(
        b.mul(c).mul(b.mul(c)),
        b.mul(b).mul(d).mul(e.mul(e)),
        a.mul(a).mul(e.mul(e)),
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        b.mul(c).mul(b.mul(c)),
        a.mul(a).mul(e.mul(e)),
        a.mul(e).mul(a.mul(e)),
    );
    // (bc)² ≤ (ae)²
    lemma_square_dominance_sum::<F>(a.mul(e), b.mul(c));
}

/// Dual dominant product: 0≤b, 0≤e, 0≤d, a²≤b²d, c²≤e²d → 0≤ac+bed.
///
/// The dominant term bed ≥ 0, and (ac)² ≤ (bed)² from the multiplication chain.
#[verifier::rlimit(20)]
proof fn lemma_dominant_product_dual<F: OrderedField>(
    a: F, b: F, c: F, e: F, d: F,
)
    requires
        F::zero().le(b),
        F::zero().le(e),
        F::zero().le(d),
        a.mul(a).le(b.mul(b).mul(d)),
        c.mul(c).le(e.mul(e).mul(d)),
    ensures
        F::zero().le(a.mul(c).add(b.mul(e).mul(d))),
{
    // bed ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b, e);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b.mul(e), d);
    // Need (ac)² ≤ (bed)²
    // From a² ≤ b²d, multiply by c² ≥ 0: a²c² ≤ (b²d)c²
    ordered_ring_lemmas::lemma_square_nonneg::<F>(c);
    F::axiom_le_mul_nonneg_monotone(a.mul(a), b.mul(b).mul(d), c.mul(c));
    // a²c² ≤ (b²d)·c²
    // From c² ≤ e²d, multiply by b²d ≥ 0: (b²d)c² ≤ (b²d)(e²d)
    ordered_ring_lemmas::lemma_square_nonneg::<F>(b);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b.mul(b), d);
    F::axiom_le_mul_nonneg_monotone(c.mul(c), e.mul(e).mul(d), b.mul(b).mul(d));
    // c²·(b²d) ≤ (e²d)·(b²d)
    F::axiom_mul_commutative(c.mul(c), b.mul(b).mul(d));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        c.mul(c).mul(b.mul(b).mul(d)),
        b.mul(b).mul(d).mul(c.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b).mul(d)),
    );
    // (b²d)c² ≤ (e²d)(b²d)
    F::axiom_le_transitive(
        a.mul(a).mul(c.mul(c)),
        b.mul(b).mul(d).mul(c.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b).mul(d)),
    );
    // a²c² ≤ (e²d)(b²d) = (bed)²
    // (ac)² ≡ a²c² by square_mul
    lemma_square_mul::<F>(a, c);
    F::axiom_eqv_symmetric(a.mul(c).mul(a.mul(c)), a.mul(a).mul(c.mul(c)));
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        a.mul(a).mul(c.mul(c)),
        a.mul(c).mul(a.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b).mul(d)),
    );
    // (e²d)(b²d) ≡ (bed)² by sq_d_product
    lemma_sq_d_product::<F>(b, e, d);
    F::axiom_eqv_symmetric(b.mul(b).mul(d).mul(e.mul(e).mul(d)), b.mul(e).mul(d).mul(b.mul(e).mul(d)));
    // swap order
    F::axiom_mul_commutative(e.mul(e).mul(d), b.mul(b).mul(d));
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        a.mul(c).mul(a.mul(c)),
        e.mul(e).mul(d).mul(b.mul(b).mul(d)),
        b.mul(b).mul(d).mul(e.mul(e).mul(d)),
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        a.mul(c).mul(a.mul(c)),
        b.mul(b).mul(d).mul(e.mul(e).mul(d)),
        b.mul(e).mul(d).mul(b.mul(e).mul(d)),
    );
    // (ac)² ≤ (bed)²
    // bed ≥ 0 → square_dominance_sum(bed, ac) → 0 ≤ bed + ac
    lemma_square_dominance_sum::<F>(b.mul(e).mul(d), a.mul(c));
    // 0 ≤ bed + ac ≡ ac + bed by commutativity
    F::axiom_add_commutative(b.mul(e).mul(d), a.mul(c));
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        F::zero(),
        b.mul(e).mul(d).add(a.mul(c)),
        a.mul(c).add(b.mul(e).mul(d)),
    );
}

/// Extract norm ≤ 0 from !(0 ≤ nx): nx ≤ 0, then le_neg_flip + neg_zero to get 0 ≤ -nx,
/// then sub_antisymmetric to get a² ≤ b²d.
proof fn lemma_norm_nonpos_to_le<F: OrderedField>(
    a2: F, b2d: F, nx: F,
)
    requires
        nx === a2.sub(b2d),
        !F::zero().le(nx),
    ensures
        a2.le(b2d),
{
    // Derive a2 ≤ b2d from !0.le(nx) where nx = a2 - b2d
    // !0.le(nx) → nx.le(0) from le_total
    F::axiom_le_total(F::zero(), nx);
    // nx + b2d ≤ 0 + b2d by add_monotone
    F::axiom_le_add_monotone(nx, F::zero(), b2d);
    // nx + b2d ≡ a2 by sub_then_add_cancel
    additive_group_lemmas::lemma_sub_then_add_cancel::<F>(a2, b2d);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        nx.add(b2d), a2, F::zero().add(b2d),
    );
    // 0 + b2d ≡ b2d
    additive_group_lemmas::lemma_add_zero_left::<F>(b2d);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        a2, F::zero().add(b2d), b2d,
    );
}

/// Extract b ≥ 0 from nonneg(x) + !(0 ≤ nx): by contradiction.
proof fn lemma_extract_im_nonneg<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires
        qe_nonneg::<F, R>(x),
        !F::zero().le(x.re.mul(x.re).sub(x.im.mul(x.im).mul(R::value()))),
    ensures
        F::zero().le(x.im),
{
    let b = x.im;
    let d = R::value();
    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
    F::axiom_le_total(F::zero(), b);
    if !F::zero().le(b) {
        // b ≤ 0 (and ¬(0 ≤ b)).
        // C1: requires 0≤b → false.
        // C3: requires 0<b → 0≤b → false.
        // C2: requires b<0 and b²d≤a² → nx≥0 → 0.le(nx). But !(0.le(nx)). Contradiction.
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(
            b.mul(b).mul(d), x.re.mul(x.re),
        );
        // If b²d ≤ a²: 0 ≤ a²-b²d = nx. But !(0≤nx). So b²d > a² in the C2 case.
        // But C2 requires b²d ≤ a². If that held, we'd have 0 ≤ nx, contradiction.
        // So C2 is impossible. All 3 cases impossible → nonneg(x) false → contradiction.
        assert(false);
    }
}

/// Product of two nonneg quadratic extension elements is nonneg.
///
/// Dispatches on le_total(0, x.re) × le_total(0, y.re), then sub-dispatches on norm signs.
/// Case A×A: 0≤a, 0≤c — 4 norm sub-cases.
/// Case A×B: 0≤a, c<0 — nonneg(y) C3 gives e>0.
/// Case B×A: a<0, 0≤c — nonneg(x) C3 gives b>0.
/// Case B×B: a<0, c<0 — both C3, trivial (ac>0, bed>0).
#[verifier::rlimit(40)]
pub proof fn lemma_nonneg_mul_closed<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
    y: SpecQuadExt<F, R>,
)
    requires
        qe_nonneg::<F, R>(x),
        qe_nonneg::<F, R>(y),
    ensures
        qe_nonneg::<F, R>(qe_mul::<F, R>(x, y)),
{
    let a = x.re; let b = x.im;
    let c = y.re; let e = y.im;
    let d = R::value();
    let z = qe_mul::<F, R>(x, y);
    let a2 = a.mul(a);
    let b2d = b.mul(b).mul(d);
    let c2 = c.mul(c);
    let e2d = e.mul(e).mul(d);
    let nx = a2.sub(b2d);
    let ny = c2.sub(e2d);

    R::axiom_value_positive();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);

    // Norm multiplicativity: nz ≡ nx · ny
    lemma_norm_mul::<F, R>(x, y);

    F::axiom_le_total(F::zero(), a);
    F::axiom_le_total(F::zero(), c);

    if F::zero().le(a) && F::zero().le(c) {
        // ═══ Case A×A: 0 ≤ a, 0 ≤ c ═══
        F::axiom_le_total(b2d, a2);
        F::axiom_le_total(e2d, c2);

        if b2d.le(a2) && e2d.le(c2) {
            // Both re-dominant. z.re ≥ 0, norm ≥ 0.
            lemma_dominant_product::<F>(a, b, c, e, d);
            ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(b2d, a2);
            ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(e2d, c2);
            ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(nx, ny);
            // norm(z) ≡ nx·ny [from lemma_norm_mul], need symmetric direction
            F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(), nx.mul(ny), qe_norm::<F, R>(z),
            );
            lemma_nonneg_conclude_re::<F, R>(z);
        } else if b2d.le(a2) && !e2d.le(c2) {
            // x re-dominant, y im-dominant. norm ≤ 0.
            // Extract e ≥ 0: nonneg(y)+0≤c → C1(e≥0) or C2(e<0 + e²d≤c², but c²<e²d, boundary).
            F::axiom_le_total(F::zero(), e);
            if F::zero().le(e) {
                // ae ≥ 0 dominant. Use cross_dominance.
                ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(b2d, a2);
                // c² ≤ e²d: !(e2d ≤ c2) + totality → c2 ≤ e2d... wait, le_total gives c2.le(e2d) || e2d.le(c2).
                // We're in !(e2d.le(c2)), so c2.le(e2d).
                // Hmm actually le_total(e2d, c2) gives e2d.le(c2) || c2.le(e2d). We're in !e2d.le(c2).
                // Wait, I called axiom_le_total(e2d, c2) which is NOT what I did. Let me re-check.
                // I called F::axiom_le_total(e2d, c2) — this should give e2d.le(c2) || c2.le(e2d).
                // If !e2d.le(c2): c2.le(e2d). ✓
                lemma_cross_dominance::<F>(a, b, c, e, d);
                // z.im ≥ 0. norm ≤ 0.
                // norm(z) ≡ nx · ny. nx ≥ 0 (b2d ≤ a2), ny ≤ 0 (c2 ≤ e2d → 0 ≤ e2d - c2 → ny ≤ 0).
                ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(b2d, a2);
                // 0 ≤ nx. And !(e2d.le(c2)) + totality → c2.le(e2d).
                ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(c2, e2d);
                // 0 ≤ e2d - c2. This means c2 - e2d ≤ 0, i.e., ny ≤ 0.
                additive_group_lemmas::lemma_sub_antisymmetric::<F>(c2, e2d);
                // c2.sub(e2d).eqv(e2d.sub(c2).neg())
                // 0 ≤ e2d.sub(c2) → (e2d.sub(c2)).neg() ≤ 0.neg() ≡ 0
                ordered_ring_lemmas::lemma_le_neg_flip::<F>(F::zero(), e2d.sub(c2));
                additive_group_lemmas::lemma_neg_zero::<F>();
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    e2d.sub(c2).neg(), F::zero().neg(), F::zero(),
                );
                // (e2d-c2).neg() ≤ 0. ny ≡ (e2d-c2).neg() → ny ≤ 0.
                F::axiom_eqv_symmetric(c2.sub(e2d), e2d.sub(c2).neg());
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    e2d.sub(c2).neg(), c2.sub(e2d), F::zero(),
                );
                // ny ≤ 0. nx ≥ 0, ny ≤ 0 → nx*ny ≤ 0.
                // Actually: 0 ≤ nx and ny ≤ 0 → nx*ny ≤ 0.
                // axiom_le_mul_nonneg_monotone(ny, 0, nx): ny ≤ 0 and 0 ≤ nx → ny*nx ≤ 0*nx = 0.
                F::axiom_le_mul_nonneg_monotone(ny, F::zero(), nx);
                ring_lemmas::lemma_mul_zero_left::<F>(nx);
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    ny.mul(nx), F::zero().mul(nx), F::zero(),
                );
                F::axiom_mul_commutative(ny, nx);
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    ny.mul(nx), nx.mul(ny), F::zero(),
                );
                // nx*ny ≤ 0. nz ≡ nx*ny. So nz ≤ 0.
                F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    nx.mul(ny), qe_norm::<F, R>(z), F::zero(),
                );
                lemma_nonneg_conclude_im::<F, R>(z);
            } else {
                // e < 0, boundary: ny ≡ 0 (from C2 of y: e²d ≤ c², combined with c² ≤ e²d).
                // norm(z) ≡ nx * 0 ≡ 0. Both z.re² ≡ z.im²d.
                // Since c ≥ 0 and b²d ≤ a² (nx ≥ 0): use dominant_product for z.re ≥ 0.
                // Wait: dominant_product needs e²d ≤ c². We have c² ≤ e²d AND e²d ≤ c² (from C2).
                // So e²d ≡ c² (boundary). e²d ≤ c² holds (from C2 of y: b²d ≤ a² form).
                // Hmm, the precondition of C2 for y: F::zero().le(c) && e.lt(F::zero()) && e²d.le(c²).
                // So e²d ≤ c² from C2. And we're in the !(e2d.le(c2)) branch... contradiction!
                // Wait: I checked axiom_le_total(e2d, c2). We're in !e2d.le(c2) branch.
                // But C2 of y requires e2d.le(c2). If !(e2d.le(c2)), C2 fails.
                // C1 requires e ≥ 0 → fails (e < 0).
                // C3 requires c < 0 → fails (c ≥ 0).
                // So nonneg(y) is false! Contradiction with requires.
                F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
                assert(false);
            }
        } else if !b2d.le(a2) && e2d.le(c2) {
            // x im-dominant, y re-dominant. Symmetric to above.
            F::axiom_le_total(F::zero(), b);
            if F::zero().le(b) {
                // bc ≥ 0 dominant. Use cross dominance (dual version — bc dominates ae).
                // a² ≤ b²d (from !b2d.le(a2) → a² ≤ b²d by totality)
                // e²d ≤ c²
                // Need: 0 ≤ ae + bc where bc ≥ 0 dominates.
                // (ae)² ≤ (bc)²: from a²≤b²d (×e²) and e²d≤c² (×b²).
                // a²e² ≤ b²de² ≡ b²(e²d) ≤ b²c². So (ae)² ≤ (bc)².
                // bc ≥ 0 → square_dominance_sum(bc, ae) → 0 ≤ bc + ae ≡ ae + bc.
                ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b, c);
                // (ae)² ≤ (bc)²
                ordered_ring_lemmas::lemma_square_nonneg::<F>(e);
                F::axiom_le_mul_nonneg_monotone(a.mul(a), b.mul(b).mul(d), e.mul(e));
                // a²e² ≤ (b²d)e²
                // (b²d)e² ≡ b²(e²d): commute
                F::axiom_mul_commutative(e.mul(e), d);
                ring_lemmas::lemma_mul_congruence_right::<F>(
                    b.mul(b), e.mul(e).mul(d), d.mul(e.mul(e)),
                );
                lemma_mul_assoc_rev::<F>(b.mul(b), d, e.mul(e));
                F::axiom_eqv_transitive(
                    b.mul(b).mul(e.mul(e).mul(d)),
                    b.mul(b).mul(d.mul(e.mul(e))),
                    b.mul(b).mul(d).mul(e.mul(e)),
                );
                F::axiom_mul_commutative(b.mul(b).mul(d), e.mul(e));
                F::axiom_eqv_transitive(
                    b.mul(b).mul(e.mul(e).mul(d)),
                    b.mul(b).mul(d).mul(e.mul(e)),
                    e.mul(e).mul(b.mul(b).mul(d)),
                );
                // Now: a²e² ≤ (b²d)e² and (b²d)e² ≡ b²(e²d)... hmm this is getting long.
                // Let me just do: a.mul(a).mul(e.mul(e)) ≤ b.mul(b).mul(d).mul(e.mul(e)).
                // b²d·e² ≡ e²·b²d by commut. And e²·(b²d) = e.mul(e).mul(b.mul(b).mul(d)).
                // axiom_le_mul_nonneg_monotone gave a²·e² ≤ b²d·e². OK.
                // Commute: b²d·e² ≡ e²·(b²d).
                // Then: e²·(b²d) ≤ ? b²c² (which is (bc)²).
                // e²d ≤ c². Multiply by b²: b²·(e²d) ≤ b²·c².
                // But we need e²·(b²d) ≤ b²c². e²·(b²d) ≡ b²·(e²d) ≡ b²d·e² (by commuting).
                // So b²·(e²d) ≤ b²·c² [from e²d ≤ c², multiply by b² ≥ 0].
                ordered_ring_lemmas::lemma_square_nonneg::<F>(b);
                F::axiom_le_mul_nonneg_monotone(e.mul(e).mul(d), c.mul(c), b.mul(b));
                // (e²d)·b² ≤ c²·b². Commute both:
                F::axiom_mul_commutative(e.mul(e).mul(d), b.mul(b));
                F::axiom_mul_commutative(c.mul(c), b.mul(b));
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    e.mul(e).mul(d).mul(b.mul(b)),
                    b.mul(b).mul(e.mul(e).mul(d)),
                    c.mul(c).mul(b.mul(b)),
                );
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    b.mul(b).mul(e.mul(e).mul(d)),
                    c.mul(c).mul(b.mul(b)),
                    b.mul(b).mul(c.mul(c)),
                );
                // b²(e²d) ≤ b²c²
                // Chain: a²e² ≤ b²d·e² ≡... hmm this is really long.
                // Let me try a different approach. I'll just use the same structure as cross_dominance
                // but with swapped roles. Actually, this IS cross_dominance_dual (b≥0, c≥0, a²≤b²d, e²d≤c²).
                // But I don't have that helper yet. Let me inline the key steps.
                // Actually the cleanest thing: I notice that z.im = ae + bc = bc + ae (by add_commutative).
                // And I can use cross_dominance with arguments (c, e, a, b, d):
                //   requires 0≤c, 0≤b, 0≤d, e²d ≤ c², a² ≤ b²d.
                //   ensures 0 ≤ c·b + e·a = bc + ea.
                // Wait: cross_dominance(a,b,c,e,d) ensures 0≤ae+bc with 0≤a, 0≤e, b²d≤a², c²≤e²d.
                // So cross_dominance(c, e, a, b, d) ensures 0≤ce+ea... no that's wrong.
                // cross_dominance signature: (a,b,c,e,d) → 0 ≤ a*e + b*c. With 0≤a,0≤e,b²d≤a²,c²≤e²d.
                // If I call cross_dominance(c, e, a, b, d): 0≤c, 0≤b (as e), e²d≤c²(as b²d≤a²), a²≤b²d(as c²≤e²d).
                // Wait: params are (a=c, b=e, c=a, e=b, d=d). Then:
                //   requires 0≤c (our c ≥ 0 ✓), 0≤b (our b ≥ 0 ✓), 0≤d ✓,
                //   b²d≤a² → e²d≤c² ✓ (we have e²d ≤ c²),
                //   c²≤e²d → a²≤b²d ✓ (we have a² ≤ b²d from !b2d.le(a2) → a2.le(b2d))
                //   ensures 0 ≤ a*e + b*c → 0 ≤ c*b + e*a = cb + ea.
                // But I need 0 ≤ ae + bc, not 0 ≤ cb + ea.
                // cb + ea = bc + ae (by mul_commut + add_commut).
                // So: cross_dominance(c, e, a, b, d) gives 0 ≤ cb + ea, and cb+ea ≡ ae+bc. ✓
                // But wait: the condition c²≤e²d maps to a²≤b²d. In our call: "c" in the cross_dominance
                // is our "a", and "e" is our "b". So condition c²≤e²d becomes a²≤b²d. ✓
                // And b²d≤a² becomes e²d≤c². ✓
                // Great! Let me just call cross_dominance with swapped args.
                lemma_cross_dominance::<F>(c, e, a, b, d);
                // 0 ≤ c*b + e*a = cb + ea
                // cb ≡ bc and ea ≡ ae by mul_commut
                F::axiom_mul_commutative(c, b);
                F::axiom_mul_commutative(e, a);
                additive_group_lemmas::lemma_add_congruence::<F>(
                    c.mul(b), b.mul(c), e.mul(a), a.mul(e),
                );
                // cb + ea ≡ bc + ae
                F::axiom_add_commutative(b.mul(c), a.mul(e));
                F::axiom_eqv_transitive(
                    c.mul(b).add(e.mul(a)),
                    b.mul(c).add(a.mul(e)),
                    a.mul(e).add(b.mul(c)),
                );
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    F::zero(),
                    c.mul(b).add(e.mul(a)),
                    a.mul(e).add(b.mul(c)),
                );
                // 0 ≤ ae + bc = z.im. ✓
                // norm ≤ 0: symmetric argument to the b2d≤a2 && !e2d≤c2 case above.
                // nx ≤ 0 (a² ≤ b²d) and ny ≥ 0 (e²d ≤ c²).
                // nx·ny ≤ 0 → nz ≤ 0.
                ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(e2d, c2);
                // ny = c2.sub(e2d). 0 ≤ ny.
                // nx: !(b2d.le(a2)) + totality → a2.le(b2d).
                ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(a2, b2d);
                // 0 ≤ b2d.sub(a2). nx = a2.sub(b2d). nx ≡ -(b2d.sub(a2)) ≤ 0.
                additive_group_lemmas::lemma_sub_antisymmetric::<F>(a2, b2d);
                ordered_ring_lemmas::lemma_le_neg_flip::<F>(F::zero(), b2d.sub(a2));
                additive_group_lemmas::lemma_neg_zero::<F>();
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    b2d.sub(a2).neg(), F::zero().neg(), F::zero(),
                );
                // (b2d-a2).neg() ≤ 0. And nx ≡ (b2d-a2).neg() [from sub_antisymmetric].
                F::axiom_eqv_symmetric(a2.sub(b2d), b2d.sub(a2).neg());
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    b2d.sub(a2).neg(), a2.sub(b2d), F::zero(),
                );
                // nx ≤ 0. ny ≥ 0. nx*ny ≤ 0.
                F::axiom_le_mul_nonneg_monotone(nx, F::zero(), ny);
                ring_lemmas::lemma_mul_zero_left::<F>(ny);
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    nx.mul(ny), F::zero().mul(ny), F::zero(),
                );
                // nz ≡ nx*ny ≤ 0.
                F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    nx.mul(ny), qe_norm::<F, R>(z), F::zero(),
                );
                lemma_nonneg_conclude_im::<F, R>(z);
            } else {
                // b < 0, boundary: nonneg(x) C2 requires b²d ≤ a². But !(b2d.le(a2)). So C2 fails.
                // C1: 0≤b → false. C3: 0<b → false. All cases fail → contradiction.
                F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
                assert(false);
            }
        } else {
            // Both im-dominant: !(b2d.le(a2)) && !(e2d.le(c2)).
            // a² ≤ b²d and c² ≤ e²d.
            // Extract b ≥ 0 and e ≥ 0.
            F::axiom_le_total(F::zero(), b);
            F::axiom_le_total(F::zero(), e);
            if F::zero().le(b) && F::zero().le(e) {
                // b ≥ 0, e ≥ 0, a ≥ 0, c ≥ 0, d > 0. All components nonneg.
                // z.re = ac + bed ≥ 0 (all terms nonneg).
                ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(a, c);
                ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b, e);
                ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b.mul(e), d);
                lemma_nonneg_add::<F>(a.mul(c), b.mul(e).mul(d));
                // norm = nx*ny ≥ 0 (both ≤ 0, product ≥ 0).
                // nx ≤ 0, ny ≤ 0. nx*ny ≥ 0.
                // From !(b2d.le(a2)) + totality: a2.le(b2d). le_iff_sub_nonneg: 0 ≤ b2d-a2.
                // nx = a2-b2d. nx ≡ -(b2d-a2) ≤ 0.
                // Similarly ny ≤ 0.
                // nx ≤ 0 and ny ≤ 0 (from !(b2d.le(a2)) → a2.le(b2d), etc.)
                lemma_sub_nonpos::<F>(a2, b2d);
                lemma_sub_nonpos::<F>(c2, e2d);
                // neg_mul_neg: nx.neg()*ny.neg() ≡ nx*ny.
                ring_lemmas::lemma_neg_mul_neg::<F>(nx, ny);
                // 0 ≤ nx.neg() and 0 ≤ ny.neg() via le_neg_flip + neg_zero:
                additive_group_lemmas::lemma_neg_zero::<F>();
                ordered_ring_lemmas::lemma_le_neg_flip::<F>(nx, F::zero());
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    F::zero().neg(), F::zero(), nx.neg(),
                );
                // 0 ≤ nx.neg() ✓
                ordered_ring_lemmas::lemma_le_neg_flip::<F>(ny, F::zero());
                ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                    F::zero().neg(), F::zero(), ny.neg(),
                );
                // 0 ≤ ny.neg() ✓
                ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(nx.neg(), ny.neg());
                // 0 ≤ nx.neg()*ny.neg() ≡ nx*ny.
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    F::zero(), nx.neg().mul(ny.neg()), nx.mul(ny),
                );
                // 0 ≤ nx*ny ≡ nz.
                F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
                ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                    F::zero(), nx.mul(ny), qe_norm::<F, R>(z),
                );
                lemma_nonneg_conclude_re::<F, R>(z);
            } else if !F::zero().le(b) {
                // b < 0. nonneg(x) C2: b<0, b²d≤a². But !(b2d.le(a2)). Contradiction.
                F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
                assert(false);
            } else {
                // e < 0. nonneg(y) C2: e<0, e²d≤c². But !(e2d.le(c2)). Contradiction.
                F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
                assert(false);
            }
        }
    } else if !F::zero().le(a) && !F::zero().le(c) {
        // ═══ Case B×B: a < 0, c < 0 ═══
        // nonneg(x) C3: a<0, b>0, a²≤b²d. nonneg(y) C3: c<0, e>0, c²≤e²d.
        // z.re = ac + bed. ac = (neg)(neg) > 0. bed = (pos)(pos)(pos) > 0. z.re > 0 → z.re ≥ 0.
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), x.im);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), y.im);
        // b > 0, e > 0 from C3 for both.
        // But we need to extract b > 0 from qe_nonneg. Z3 should see C3 since a < 0 rules out C1/C2.
        // a < 0: axiom_lt_iff_le_and_not_eqv(a, 0): a.le(0) && !a.eqv(0).
        F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
        F::axiom_lt_iff_le_and_not_eqv(c, F::zero());

        // ac > 0: (-a)(-c) ≡ ac by neg_mul_neg. And (-a) > 0, (-c) > 0.
        // (-a) ≥ 0 and (-c) ≥ 0:
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(a, F::zero());
        additive_group_lemmas::lemma_neg_zero::<F>();
        // 0.neg().le(a.neg()) from neg_flip, 0.neg() ≡ 0 from neg_zero → 0.le(a.neg())
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), a.neg(),
        );
        // 0 ≤ a.neg(). Similarly:
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(c, F::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), c.neg(),
        );
        // 0 ≤ c.neg().
        ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(a.neg(), c.neg());
        ring_lemmas::lemma_neg_mul_neg::<F>(a, c);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(), a.neg().mul(c.neg()), a.mul(c),
        );
        // 0 ≤ ac ✓

        // Extract b ≥ 0 and e ≥ 0 from C3 (a < 0 rules out C1/C2, so C3 gives 0.lt(b)):
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), e);
        // bed ≥ 0:
        ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b, e);
        ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(b.mul(e), d);

        // z.re ≥ 0
        lemma_nonneg_add::<F>(a.mul(c), b.mul(e).mul(d));

        // norm ≥ 0: nx ≤ 0, ny ≤ 0 → nx*ny ≥ 0.
        // nx ≤ 0: a² ≤ b²d from C3. le_iff_sub_nonneg: 0 ≤ b2d - a2.
        // So a2.sub(b2d) ≡ (b2d.sub(a2)).neg() ≤ 0.
        // Extract nx ≤ 0 from nonneg + a < 0 (C3):
        // C3 gives a² ≤ b²d and c² ≤ e²d. So nx = a²-b²d ≤ 0, ny = c²-e²d ≤ 0.
        lemma_sub_nonpos::<F>(a2, b2d);
        lemma_sub_nonpos::<F>(c2, e2d);
        // neg_mul_neg + nonneg_mul_nonneg:
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(nx, F::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), nx.neg(),
        );
        ordered_ring_lemmas::lemma_le_neg_flip::<F>(ny, F::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<F>(
            F::zero().neg(), F::zero(), ny.neg(),
        );
        ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(nx.neg(), ny.neg());
        ring_lemmas::lemma_neg_mul_neg::<F>(nx, ny);
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(), nx.neg().mul(ny.neg()), nx.mul(ny),
        );
        F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
        ordered_ring_lemmas::lemma_le_congruence_right::<F>(
            F::zero(), nx.mul(ny), qe_norm::<F, R>(z),
        );
        lemma_nonneg_conclude_re::<F, R>(z);
    } else if F::zero().le(a) && !F::zero().le(c) {
        // ═══ Case A×B: 0 ≤ a, c < 0 ═══
        // nonneg(y) C3: c<0, e>0, c²≤e²d.
        // e > 0 from C3. ae ≥ 0 (a≥0, e≥0).
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), y.im);
        // le_total(b²d, a²):
        F::axiom_le_total(b2d, a2);
        if b2d.le(a2) {
            // nx ≥ 0, ny ≤ 0. norm ≤ 0. Need z.im ≥ 0.
            // cross_dominance(a,b,c,e,d): ae dominant.
            lemma_cross_dominance::<F>(a, b, c, e, d);
            // z.im ≥ 0 ✓
            // Show norm ≤ 0: nx ≥ 0, ny ≤ 0 → nx*ny ≤ 0.
            ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(b2d, a2);
            // C3 of y: c² ≤ e²d. ny = c²-e²d ≤ 0.
            lemma_sub_nonpos::<F>(c2, e2d);
            // ny ≤ 0 ✓, nx ≥ 0 ✓
            F::axiom_le_mul_nonneg_monotone(ny, F::zero(), nx);
            ring_lemmas::lemma_mul_zero_left::<F>(nx);
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                ny.mul(nx), F::zero().mul(nx), F::zero(),
            );
            F::axiom_mul_commutative(ny, nx);
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                ny.mul(nx), nx.mul(ny), F::zero(),
            );
            F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                nx.mul(ny), qe_norm::<F, R>(z), F::zero(),
            );
            lemma_nonneg_conclude_im::<F, R>(z);
        } else {
            // a² ≤ b²d (nx ≤ 0). ny ≤ 0 (from C3 of y). norm ≥ 0 (neg*neg).
            // Need z.re ≥ 0. b ≥ 0 (extract from nonneg(x) + !(b2d.le(a2))):
            // If b < 0: C2 requires b²d ≤ a² → contradicts !(b2d.le(a2)). C1: b≥0→contradiction. C3: b>0→b≥0.
            // So if !(b≥0): all cases of nonneg(x) fail → contradiction.
            // b ≥ 0: nonneg(x) with 0.le(a) → C1 or C2. C2 requires b2d.le(a2), contradicts !b2d.le(a2). So C1: b≥0.
            if !F::zero().le(b) {
                // Rule out C3: a.lt(0) is false since 0.le(a).
                F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
                F::axiom_le_total(a, F::zero());
                if a.le(F::zero()) {
                    F::axiom_le_antisymmetric(a, F::zero());
                    // a.eqv(0) contradicts !a.eqv(0) from lt_iff. So a.lt(0) false.
                }
                // C1 fails (!0.le(b)), C2 fails (!b2d.le(a2)), C3 fails (!a.lt(0)).
                assert(false);
            }
            // b ≥ 0 ✓. e > 0 ≥ 0 from C3 of y.
            // dominant_product_dual(a,b,c,e,d): 0≤b, 0≤e, 0≤d, a²≤b²d, c²≤e²d → 0≤ac+bed.
            lemma_dominant_product_dual::<F>(a, b, c, e, d);
            // z.re ≥ 0 ✓
            // norm ≥ 0: both nx ≤ 0 and ny ≤ 0 → neg_mul_neg.
            lemma_sub_nonpos::<F>(c2, e2d);
            lemma_sub_nonpos::<F>(a2, b2d);
            ring_lemmas::lemma_neg_mul_neg::<F>(nx, ny);
            additive_group_lemmas::lemma_neg_zero::<F>();
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(nx, F::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                F::zero().neg(), F::zero(), nx.neg(),
            );
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(ny, F::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                F::zero().neg(), F::zero(), ny.neg(),
            );
            ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(nx.neg(), ny.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(), nx.neg().mul(ny.neg()), nx.mul(ny),
            );
            F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(), nx.mul(ny), qe_norm::<F, R>(z),
            );
            lemma_nonneg_conclude_re::<F, R>(z);
        }
    } else {
        // ═══ Case B×A: a < 0, 0 ≤ c ═══
        // nonneg(x) C3: a<0, b>0, a²≤b²d.
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), x.im);
        F::axiom_le_total(e2d, c2);
        if e2d.le(c2) {
            // ny ≥ 0, nx ≤ 0. norm ≤ 0. Need z.im ≥ 0.
            // bc ≥ 0 (b>0→b≥0, c≥0). cross_dominance with swapped args:
            // cross_dominance(c, e, a, b, d): 0≤c, 0≤b, e²d≤c², a²≤b²d → 0 ≤ c*b + e*a.
            // 0 ≤ b from C3 (lt_iff above gives le + not_eqv).
            lemma_cross_dominance::<F>(c, e, a, b, d);
            // 0 ≤ cb + ea ≡ ae + bc
            F::axiom_mul_commutative(c, b);
            F::axiom_mul_commutative(e, a);
            additive_group_lemmas::lemma_add_congruence::<F>(
                c.mul(b), b.mul(c), e.mul(a), a.mul(e),
            );
            F::axiom_add_commutative(b.mul(c), a.mul(e));
            F::axiom_eqv_transitive(
                c.mul(b).add(e.mul(a)),
                b.mul(c).add(a.mul(e)),
                a.mul(e).add(b.mul(c)),
            );
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(),
                c.mul(b).add(e.mul(a)),
                a.mul(e).add(b.mul(c)),
            );
            // z.im ≥ 0 ✓
            // norm ≤ 0: nx ≤ 0 (from C3: a²≤b²d), ny ≥ 0.
            lemma_sub_nonpos::<F>(a2, b2d);
            // nx ≤ 0 ✓
            ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<F>(e2d, c2);
            // ny ≥ 0 ✓
            F::axiom_le_mul_nonneg_monotone(nx, F::zero(), ny);
            ring_lemmas::lemma_mul_zero_left::<F>(ny);
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                nx.mul(ny), F::zero().mul(ny), F::zero(),
            );
            // nx*ny ≤ 0 ✓. Transfer to qe_norm(z) ≤ 0:
            F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                nx.mul(ny), qe_norm::<F, R>(z), F::zero(),
            );
            lemma_nonneg_conclude_im::<F, R>(z);
        } else {
            // c² ≤ e²d, nx ≤ 0, ny ≤ 0. norm ≥ 0. Need z.re ≥ 0.
            // b ≥ 0 from C3 of x (lt_iff at line above gives 0.le(b)).
            // e ≥ 0: nonneg(y) with 0.le(c) → C1 or C2. C2 needs e2d.le(c2), contradicts !e2d.le(c2). So C1: e≥0.
            if !F::zero().le(y.im) {
                // Rule out C3 of y: c.lt(0) is false since 0.le(c).
                F::axiom_lt_iff_le_and_not_eqv(c, F::zero());
                F::axiom_le_total(c, F::zero());
                if c.le(F::zero()) {
                    F::axiom_le_antisymmetric(c, F::zero());
                }
                // C1 fails (!0.le(e)), C2 fails (!e2d.le(c2)), C3 fails (!c.lt(0)).
                assert(false);
            }
            // b ≥ 0, e ≥ 0.
            // dominant_product_dual: 0≤b, 0≤e, 0≤d, a²≤b²d, c²≤e²d → 0≤ac+bed.
            lemma_dominant_product_dual::<F>(a, b, c, e, d);
            // z.re ≥ 0 ✓
            // norm ≥ 0: both nx ≤ 0 and ny ≤ 0 → neg_mul_neg.
            lemma_sub_nonpos::<F>(a2, b2d);
            lemma_sub_nonpos::<F>(c2, e2d);
            ring_lemmas::lemma_neg_mul_neg::<F>(nx, ny);
            additive_group_lemmas::lemma_neg_zero::<F>();
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(nx, F::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                F::zero().neg(), F::zero(), nx.neg(),
            );
            ordered_ring_lemmas::lemma_le_neg_flip::<F>(ny, F::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<F>(
                F::zero().neg(), F::zero(), ny.neg(),
            );
            ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(nx.neg(), ny.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(), nx.neg().mul(ny.neg()), nx.mul(ny),
            );
            F::axiom_eqv_symmetric(qe_norm::<F, R>(z), nx.mul(ny));
            ordered_ring_lemmas::lemma_le_congruence_right::<F>(
                F::zero(), nx.mul(ny), qe_norm::<F, R>(z),
            );
            lemma_nonneg_conclude_re::<F, R>(z);
        }
    }
}

} // verus!
