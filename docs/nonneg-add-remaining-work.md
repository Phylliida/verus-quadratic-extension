# DTS nonneg_add_remaining — Session 9 Status (2026-04-10)

## Current State: 142 verified, 1 error (+ 9 pre-existing axiom_non_square)

The `nonneg_add_remaining` dispatch handles 4 of 6 factor C-class
combinations. The C2+C3 / C3+C2 case is algebraically **SOLVED**
(see "SOLVED Algebraic Plan" below) — the cancellation primitive
is in place, and the two helpers (`c2c3_norm_bound` /
`c2c3_neg_norm_bound`) plus dispatch wiring remain as implementation
work for the next session.

**Session 9 delta vs Session 8:**
- Added `lemma_dts_le_mul_cancel_pos_fuel` at `decreases (fuel, 3nat)`
  (~200 lines, VERIFIED). Cancellation by a positive factor, needed
  by the c2c3 approach. (+1 verified from 141 → 142.)
- Discovered √d-free algebraic plan via cancellation-by-b1² strategy.
- The 1 remaining error is unchanged (C2+C3 postcondition in
  `nonneg_add_remaining`).

## Session 8 Progress (2026-04-10)

Built on Session 7's foundations (`cauchy_cross_term`, `c2c2_norm_bound`,
`norm_sum_decomposition` etc.) and implemented:

### New helpers (all VERIFIED)

1. **`lemma_dts_cauchy_cross_term_neg`** (~280 lines, decreases (f, 4nat))
   Negative-norm version of cauchy_cross_term. From neg-norms (d*bi² ≥ ai²),
   nonneg(a1*a2), nonneg(d*b1*b2), derives nonneg(d*b1*b2 - a1*a2).
   Composes existing `lemma_cauchy_le_chain_neg_norms` + `dd_sq_product_eqv`
   + `square_of_product` + `square_le_implies_le`.

2. **`lemma_dts_c3c3_neg_norm_bound`** (~670 lines, decreases (f, 5nat))
   Mirrors `c2c2_norm_bound` but for negative norms. Uses
   `cauchy_cross_term_neg` + `norm_sum_decomposition` + a 3-step neg-distribution
   chain (`neg_add` × 3 + `add_congruence_left/right` + `eqv_transitive`).
   Output: `nonneg(sub(d*ssb², ssa²))`.

3. **`lemma_dts_c1c3_neg_norm_bound`** (~660 lines, decreases (f, 1nat))
   Mirrors `c1c2_norm_bound` with the chain reversed: T1: d*sum_im² ≥ d*s²,
   T2: d*s² ≥ r² (from C3 neg-norm), T3: r² ≥ sum_re² (via square_le_square
   on negs). Final via 2× `sub_add_sub` telescope.

### `nonneg_add_remaining` body — REWRITTEN

Replaces the previous WIP body that had a `f+1` termination violation.
New structure dispatches on factor C-classes (extracted from the
`nonneg_fuel(x_ext, f+1)` precondition), routing to the correct helper:

| Combination | Path | Status |
|-------------|------|--------|
| C2+C2 | `c2c2_norm_bound` + `conclude_re_fuel` | ✅ VERIFIED |
| C3+C3 | `c3c3_neg_norm_bound` + `conclude_im_fuel` | ✅ VERIFIED |
| C1+C3 / C3+C1 | `c1c3_neg_norm_bound` + `conclude_im_fuel` (sum_re<0)<br>or trivial C1 (sum_re≥0) | ✅ VERIFIED |
| C2+C3 / C3+C2 | TODO (needs c2c3 helpers) | ❌ ERROR |

For C3+C3 and C1+C3, used `lemma_dts_nonneg_sum_zero_implies_zero` to
derive contradictions when `is_zero(sum_im)` (since C3 has `!is_zero(b_c3)`).

The `nonneg_add_remaining` function is at `decreases (f, 8nat)`. All
helper calls respect termination (the c2c2/c3c3 helpers are at (f, 5nat),
c1c3 at (f, 1nat), cauchy_cross_term_neg at (f, 4nat)).

## Remaining: C2+C3 / C3+C2 case

This is the algebraically hardest case. From one factor in C2 (a≥0, b<0,
a²≥d*b²) and other in C3 (a<0, b≥0, d*b²≥a²), the sum can land in any
of Cases 1, 2, 3 (and Case 4 is impossible).

### Case 1 (sum_re≥0, sum_im≥0): trivially handled (already in code)

### Cases 2 & 3 — algebraically hard

The mathematical proof exists but requires √d explicitly, which DTS
doesn't have as a value:

**Case 2 (sum_re≥0, sum_im<0): need (a_c2-|a_c3|)² ≥ d*(|b_c2|-b_c3)²**

The "natural" proof: from a_c2 ≥ √d*|b_c2| (C2 norm + nonneg) and
√d*b_c3 ≥ |a_c3| (C3 neg-norm + nonneg), add and rearrange to
a_c2 - |a_c3| ≥ √d*(|b_c2| - b_c3). Both sides nonneg in Case 2.
Square: (a_c2-|a_c3|)² ≥ d*(|b_c2|-b_c3)². ✓

**The challenge**: square_le_implies_le converts squared inequalities to
linear (root) inequalities, but constructing intermediate `√d*|b_c2|`
values requires √d as a DTS value (which doesn't exist at the current
level — √d would be a *higher* level).

### Algebraic explorations attempted (all dead-ended)

- **Cross-term analysis**: `sum_re² - d*sum_im² = A - B + 2*cross_mod`
  where A = norm of C2 side (≥0), B = neg-norm of C3 side (≥0),
  cross_mod = `d*|b_c2|*b_c3 - a_c2*|a_c3|`. The cross_mod sign is
  uncertain; counter-examples exist where cross_mod < 0 yet the goal
  holds (because A is large enough to compensate).

- **Identity**: `A*B + cross_mod² = d*(a_c2*b_c3 - |b_c2|*|a_c3|)²`.
  Mathematically beautiful but doesn't directly give a sign on
  cross_mod.

- **Imaginary cross**: Q = a_c2*b_c3 - |b_c2|*|a_c3| is provably ≥ 0 in
  C2+C3 (via squared chain: a_c2²*b_c3² ≥ |b_c2|²*|a_c3|² →
  square_le_implies_le with both nonneg). But translating Q ≥ 0 into a
  bound on `sum_re² - d*sum_im²` requires another √d-explicit step.

- **Difference of squares factoring**:
  `sum_re² - d*sum_im² = (sum_re - √d*sum_im)*(sum_re + √d*sum_im)`.
  In Case 2, the first factor is positive trivially, and the second
  is nonneg via the C2+C3 conditions — but again √d is needed.

- **Argument permutations**: Tried plugging C3 facts into
  `lemma_cauchy_le_transitive_raw` (needs both norms positive),
  `lemma_cauchy_le_chain_neg_norms` (needs both negative), and
  `cauchy_cross_term` variants. None work for the mixed-sign C2+C3.

### SOLVED Algebraic Plan (Session 9, 2026-04-10)

The natural proof uses √d explicitly, but there is a √d-FREE chain via
a **cancellation-by-b₁²** strategy. The key insight: we don't need √d
as a value — we can prove the goal "scaled by B²" and then cancel B².

Let A = a₁ (≥0), B = −b₁ (≥0, >0 in Case 2), C = −a₂ (≥0), D = b₂ (≥0).
Case 2: A ≥ C (sum_re ≥ 0), B > D (sum_im < 0).
Case 3: C ≥ A (sum_re < 0), D ≥ B (sum_im > 0) — cancel by D² instead.

**Key derivation (Case 2):**

Step 1: `a1·b2 ≥ b1·a2` (equivalent to AD ≥ BC) via squared chain:
  - From `a1² ≥ d·b1²` (C2) scale by b2²: `a1²·b2² ≥ d·b1²·b2²`
  - From `d·b2² ≥ a2²` (C3) scale by b1²: `d·b1²·b2² ≥ b1²·a2²`
  - Chain: `a1²·b2² ≥ b1²·a2²`, i.e., `(a1·b2)² ≥ (b1·a2)²`
  - Apply `square_le_implies_le_fuel` with both `a1·b2, b1·a2 ≥ 0`
    (the latter via `neg(b1)·neg(a2) = b1·a2` and both factors ≥ 0)
  - → `a1·b2 ≥ b1·a2`, i.e., `nonneg(sub(a1·b2, b1·a2))`

Step 2: Distribute: `sum_re·neg(b1) − neg(sum_im)·a1 ≡ a1·b2 − b1·a2`
  - `sum_re·neg(b1) = (a1+a2)·(−b1) = −a1·b1 − a2·b1`
  - `neg(sum_im)·a1 = (−(b1+b2))·a1 = −a1·b1 − a1·b2`
  - Difference: `(−a1·b1 − a2·b1) − (−a1·b1 − a1·b2) = a1·b2 − a2·b1`
  - Apply distributivity lemmas + neg_mul chains; transfer nonneg

Step 3: Square-monotonicity via `lemma_dts_square_le_square_fuel`:
  - From `nonneg(sum_re·neg(b1) − neg(sum_im)·a1)` get
    `(sum_re·neg(b1))² ≥ (neg(sum_im)·a1)²`
  - i.e., `sum_re²·b1² ≥ sum_im²·a1²` (using `neg(x)² = x²` + square_of_product)

Step 4: Chain with C2 via `le_mul_nonneg_monotone_fuel`:
  - Scale C2 (`a1² − d·b1² ≥ 0`) by `sum_im² ≥ 0` (via `square_nonneg`)
  - → `sum_im²·a1² − sum_im²·d·b1² ≥ 0`
  - i.e., `sum_im²·a1² ≥ sum_im²·d·b1²`

Step 5: Transitive chain:
  - `sum_re²·b1² ≥ sum_im²·a1² ≥ d·sum_im²·b1²`
  - Rearrange via mul_commutative/associative: `sum_re²·b1² ≥ (d·sum_im²)·b1²`

Step 6: Cancel `b1²` using `lemma_dts_le_mul_cancel_pos_fuel` (ADDED):
  - `nonneg(b1²)` via `square_nonneg`
  - `!is_zero(b1²)` via `mul_cancel_zero` contrapositive on `!is_zero(b1)`
  - `!is_zero(b1)` is derivable from Case 2 conditions (if `b1 = 0` then
    `sum_im = b2 ≥ 0`, contradicting `!nonneg(sum_im)`)
  - → `sum_re² ≥ d·sum_im²`, which is the goal (modulo `neg(sum_im)² = sum_im²`).

**Symmetry for Case 3 (sum_re<0, sum_im≥0):** Mirror the chain, cancel by `b2²`.
The analogous linear fact is `a2·b1 ≥ a1·b2` — wait, that's the *reverse* of
Case 2's fact. Actually we still need `a1·b2 ≥ b1·a2` (same squared chain),
but now we write the linear distribution as
`neg(sum_re)·b2 − sum_im·neg(a2) ≡ b1·a2·(−1) + a1·b2·(−1)·(−1) = a1·b2 − b1·a2`
(or similar — the sign analysis needs care). The squared chain,
`sum_re²·b2² ≥ sum_im²·a2²` ≥ `sum_im²·(d·b2²)/... `, ends up cancelling `b2²`
using `!is_zero(b2)` (derivable from Case 3 conditions: if `b2 = 0` then
`sum_re = a1 + a2` with `a1 ≥ 0`, `a2 ≤ 0` and no immediate contradiction —
but C3 requires `!is_zero(b2)` so this might actually be a precondition).
**Implementation note:** the exact sign choreography should be worked out
while writing the helper, ideally by translating the A,B,C,D argument back
carefully. Case 3 is symmetric to Case 2 under x ↔ y swap, so the cleanest
approach may be to call `c2c3_norm_bound(a2, b2, a1, b1, ...)` with swapped
arguments and then congruence the result.

**Case 4 (both sum_re<0, sum_im<0) is impossible — squared proof:**
From Case 4 we have `!is_zero(sum_im)` and sum_im < 0. With `nonneg(b2)` (C3)
and `nonneg(neg(b1))` (C2), this forces `neg(b1) > b2` strictly (since their
sum is negative). So `b1² > b2²` strictly. Chain:
- `a1² ≥ d·b1²` (C2)
- `d·b1² > d·b2²` (strict, from `b1² > b2²`)
- `d·b2² ≥ a2²` (C3)
- So `a1² > a2²` strictly.
- With `a1 ≥ 0` and `neg(a2) ≥ 0`, square_le_implies_le gives `a1 > neg(a2)`,
  i.e., `a1 + a2 > 0`, i.e., `sum_re > 0`, contradicting `!nonneg(sum_re)`.

The strict inequalities are tricky in DTS — `b1² > b2²` strict needs care.
One approach: derive `nonneg(sub(b1², b2²))` via `square_le_square_fuel` on
`neg(b1) ≥ b2` (from `neg(b1) − b2 = neg(sum_im) ≥ 0` and Case 4's
`!is_zero(sum_im)` giving strict inequality). Then the chain above gives
`nonneg(sub(a1², a2²))` eventually, and combined with `!is_zero(sum_re)` +
the squared linearization, we get a contradiction.

### Session 9 Status

- **DONE**: `lemma_dts_le_mul_cancel_pos_fuel` — cancellation lemma at
  `decreases (fuel, 3nat)`. Uses le_antisymmetric + mul_cancel_zero
  (integral domain) via contradiction. ~200 lines. VERIFIED. Located
  immediately after `lemma_dts_le_mul_nonneg_monotone_fuel` in
  `src/dyn_tower_lemmas.rs` (~line 10230).

- **TODO**: `lemma_dts_c2c3_norm_bound` — Case 2 helper. Large (~700+
  lines) due to extensive sr/wf plumbing at each chain step. Target
  `decreases (fuel, 6nat)` so it can call cancellation at (fuel, 3nat),
  square_le_square at (fuel, 2nat), le_mul_nonneg_monotone at (fuel, 2nat),
  square_le_implies_le at (fuel, 1nat). Insert before line 14489 (before
  the `nonneg_add_remaining` doc comment).

- **TODO**: `lemma_dts_c2c3_neg_norm_bound` — Case 3 mirror. Same
  structure, cancel by `b2²` instead of `b1²`. Alternatively, reuse
  `c2c3_norm_bound` via argument swap + result congruence.

- **TODO**: Wire dispatch in `nonneg_add_remaining` — Case 1 trivial
  (already done), Case 2 via `c2c3_norm_bound` + `conclude_re_fuel`,
  Case 3 via `c2c3_neg_norm_bound` + `conclude_im_fuel`, Case 4
  contradiction via the squared-inequality argument above.

### Original possible paths (for reference)

1. **Extend the field**: Define a "scaled" version of the problem where
   we work with (a, √d*b) pairs and avoid raw √d. Probably requires a
   new spec function and considerable plumbing. NOT NEEDED.

2. **Inline brute force**: Write a ~1000+ line c2c3 helper that
   manipulates the algebraic identity directly via `le_mul_nonneg_monotone`
   chains. **← This is the approach adopted, via cancellation strategy.**

3. **Reduce to multiplication**: Use `nonneg_mul_closed` on x_ext, y_ext.
   This requires fuel f+1 which violates termination at decreases (f, 8nat).
   To enable: restructure the entire nonneg_add / nonneg_mul mutual
   recursion to give nonneg_add_remaining a higher fuel bucket. Major
   refactor. NOT NEEDED.

4. **New algebraic helper**: Write a "mixed Cauchy" helper that takes
   one positive norm and one negative norm and produces some useful
   intermediate fact. The identity
   `(a_c2² - d*|b_c2|²)(d*b_c3² - |a_c3|²) ≥ 0` might be a starting
   point, expanded out. NOT NEEDED (the cancellation approach is cleaner).

## File Locations

All in `verus-quadratic-extension/src/dyn_tower_lemmas.rs`:

| Function | Line | Status |
|----------|------|--------|
| `lemma_dts_le_mul_nonneg_monotone_fuel` | ~10129 | VERIFIED (pre-existing) |
| `lemma_dts_le_mul_cancel_pos_fuel` | ~10230 | **✅ VERIFIED (session 9)** |
| `lemma_dts_cauchy_cross_term_neg` | ~12010 | ✅ VERIFIED (session 8) |
| `lemma_dts_c2c2_norm_bound` | ~12283 | ✅ VERIFIED (session 7) |
| `lemma_dts_c3c3_neg_norm_bound` | ~12654 | ✅ VERIFIED (session 8) |
| `lemma_dts_norm_sum_decomposition` | ~13325 | ✅ VERIFIED (session 7) |
| `lemma_dts_c1c3_neg_norm_bound` | ~13543 | ✅ VERIFIED (session 8) |
| `lemma_dts_c2c3_norm_bound` | TBD (~14489) | ❌ TODO (session 10) |
| `lemma_dts_c2c3_neg_norm_bound` | TBD (~14489) | ❌ TODO (session 10) |
| `lemma_dts_nonneg_add_remaining` | ~14496 | ❌ 1 error (c2c3 case) |
| `lemma_dts_nonneg_add_closed_fuel` | ~14648 | ❌ 1 error (cascades from above) |

## Decreases Hierarchy (Updated for Session 9)

| Function | Decreases | Status |
|----------|-----------|--------|
| `nonneg_mul_closed` | (fuel, 0nat) | VERIFIED |
| `nonneg_add_closed` | (fuel, 0nat) | trusts helper |
| `cauchy_schwarz_step` | (fuel, 1nat) | VERIFIED |
| `c1c3_neg_norm_bound` | (fuel, 1nat) | VERIFIED (session 8) |
| `square_le_implies_le` | (fuel, 1nat) | VERIFIED |
| `le_antisymmetric` | (fuel, 1nat) | VERIFIED |
| `square_le_square` | (fuel, 2nat) | VERIFIED |
| `le_mul_nonneg_monotone` | (fuel, 2nat) | VERIFIED |
| `nonneg_or_neg_nonneg` | (fuel, 2nat) | VERIFIED |
| `le_mul_cancel_pos` | (fuel, 3nat) | **VERIFIED (session 9)** |
| `cauchy_cross_term` | (fuel, 4nat) | VERIFIED (session 7) |
| `cauchy_cross_term_neg` | (fuel, 4nat) | VERIFIED (session 8) |
| `c2c2_norm_bound` | (fuel, 5nat) | VERIFIED (session 7) |
| `c3c3_neg_norm_bound` | (fuel, 5nat) | VERIFIED (session 8) |
| `c2c3_norm_bound` | (fuel, 6nat) | **planned (session 10)** |
| `c2c3_neg_norm_bound` | (fuel, 6nat) | **planned (session 10)** |
| `nonneg_add_remaining` | (fuel, 8nat) | 1 error (c2c3 case) |
| `nonneg_mul_remaining` | (fuel, 9nat) | VERIFIED |

## Z3 Context Pollution Lessons (Updated)

In addition to lessons from Sessions 4-7:

8. **Symmetry direction in same_radicand_symmetric**: `sym(a, b)` requires
   `sr(a, b)` and gives `sr(b, a)`. Easy to flip the wrong way and get
   precondition failure. When in doubt, build explicit chain via `a1` or
   another anchor point.

9. **Build wf for sub() expressions BEFORE using them**: `sub(a, b)` is
   really `add(a, neg(b))`, so wf requires sr(a, neg(b)), which needs
   wf(neg(b)) (via `neg_well_formed`), `same_radicand_neg(b)`, and
   sym chain. Pattern: setup neg first, then sr chain, then add_closed.

10. **`lemma_dts_is_zero_congruence` vs `lemma_dts_is_zero_eqv`**: The
    former takes is_zero + eqv → is_zero (transitive). The latter takes
    is_zero + is_zero → eqv. Confused these multiple times.

11. **`nonneg_sum_zero_implies_zero` for !is_zero contradictions**: When
    you need !is_zero(b1+b2) and have nonneg(b1), nonneg(b2), !is_zero(b1):
    if dts_is_zero(b1+b2), apply this lemma to derive is_zero(b1),
    contradicting the precondition.
