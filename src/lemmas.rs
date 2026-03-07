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

} // verus!
