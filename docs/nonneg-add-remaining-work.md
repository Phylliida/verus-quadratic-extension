# DTS nonneg_add_remaining — COMPLETE (2026-04-13)

## Final State: 150 verified, 0 errors

**`lemma_dts_nonneg_add_closed_fuel` is FULLY VERIFIED.** DTS nonnegativity
is proved closed under addition across all C-class combinations in dynamic
towers of quadratic field extensions. Zero assumes, zero admits, zero
external_body.

Combined with `nonneg_mul_closed` (completed earlier), this establishes
that the nonneg cone in DTS is closed under both addition and multiplication
— the two hardest pillars of the OrderedField proof.

## Session 10 (2026-04-13) — Final push

### New helpers (all VERIFIED)

1. **`lemma_dts_c2c3_neg_norm_bound`** (~1675 lines, decreases (f, 6nat))
   Case 3 mirror of `c2c3_norm_bound`. Cancellation-by-b2² strategy.
   From C2+C3 with Case 3 signs (neg(sum_re)≥0, sum_im≥0), derives
   `nonneg(sub(d·sum_im², sum_re²))` — the C3 neg-norm form.

2. **`lemma_dts_norm_transfer`** (~200 lines, decreases (f, 0nat))
   Generic helper: given `eqv(xp, x)` and `eqv(yp, y)`, transfers
   `nonneg(sub(xp², d·yp²))` to `nonneg(sub(x², d·y²))` (and reverse).
   Used for C3+C2 dispatch where helpers use add(a2,a1) but postcondition
   needs add(a1,a2).

3. **`lemma_dts_c2c3_iszero_sum_im_implies_nonneg_sum_re`** (~300 lines, decreases (f, 4nat))
   Contradiction: `is_zero(b1+b2)` with C2+C3 norms implies `nonneg(a1+a2)`.
   Proof: b2=neg(b1) → b2²=b1² → d·b2²=d·b1² → chain a1²≥a2² →
   `square_le_implies_le` → a1≥|a2| → nonneg(sum_re).

4. **`lemma_dts_c2c3_case4_contradiction`** (~350 lines, decreases (f, 5nat))
   Generalizes #3: `nonneg(neg(b1+b2))` implies `nonneg(a1+a2)`.
   Proof: neg(b1+b2)≥0 → sub(neg(b1), b2)≥0 → `square_le_square` →
   b1²≥b2² → `le_mul_nonneg_monotone` → d·b1²≥d·b2² → chain a1²≥a2² →
   `square_le_implies_le` → nonneg(sum_re). Contradicts Case 4's
   `!nonneg(sum_re)`.

5. **`proof_unreachable_nonneg_add_remaining`** (~15 lines)
   Boolean exhaustion helper with clean Z3 context. Proves that
   the 6 handled C-class combos + the 3 caller-excluded combos cover
   all 9 possibilities.

### Dispatch structure (final)

`nonneg_add_closed_fuel` handles C1+C1, C1+C2, C2+C1 directly, then calls
`nonneg_add_remaining` with precondition `!(a1_nn && a2_nn && (b1_nn || b2_nn))`.

`nonneg_add_remaining` dispatches:

| Combination | Handler | How |
|-------------|---------|-----|
| C2+C2 | `c2c2_norm_bound` + `conclude_re` | Direct |
| C3+C3 | `c3c3_neg_norm_bound` + `conclude_im` | Direct |
| C1+C3 | `c1c3_neg_norm_bound` + `conclude_im` | Direct |
| C3+C1 | `c1c3_neg_norm_bound` + `conclude_im` | Direct (dup) |
| C2+C3 | Cases 1-4 inline | See below |
| C3+C2 | Cases 1-4 via norm_transfer | Swapped args |

C2+C3 / C3+C2 sub-dispatch:
- **Case 1** (sum_re≥0, sum_im≥0): trivial C1
- **Case 2** (sum_re≥0, neg(sum_im)≥0): `c2c3_norm_bound` → `conclude_re`
- **Case 3** (neg(sum_re)≥0, sum_im≥0): `c2c3_neg_norm_bound` → `conclude_im`
  - is_zero(sum_im) sub-case: `iszero_sum_im_implies_nonneg_sum_re` → contradiction
- **Case 4** (neg(sum_re)≥0, neg(sum_im)≥0): `case4_contradiction` → contradiction

For C3+C2: call helpers with (a2, b2, a1, b1), transfer results via
`norm_transfer` + `add_commutative` congruence chains.

## Session 9b (2026-04-10)

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

### Session 9b Status (2026-04-10) — c2c3_norm_bound milestone

- **DONE**: `lemma_dts_c2c3_ab_linear` at `decreases (fuel, 4nat)`
  (~740 lines, VERIFIED). Linear cross-term bound: from C2 norm
  (a1²≥d·b1²) and C3 neg-norm (d·b2²≥a2²), derives
  `nonneg(sub(a1·b2, b1·a2))` via squared chain
  `(a1·b2)² ≥ (b1·a2)²` + `square_le_implies_le_fuel`. The
  second-side nonneg `b1·a2 ≥ 0` is derived via `neg(b1)·neg(a2) ≡ b1·a2`
  with both factors nonneg from C2/C3 conditions.
  Located ~line 14498 of dyn_tower_lemmas.rs.

- **DONE**: `lemma_dts_c2c3_norm_bound` at `decreases (fuel, 6nat)`
  (~1500 lines, VERIFIED). Implements all 7 steps of the cancellation-by-b1²
  strategy from session 9 doc. From C2 (a1²≥d·b1²), C3 (d·b2²≥a2²), and
  Case 2 sum signs (sum_re≥0, neg(sum_im)≥0), plus the C2 side's
  `!is_zero(b1)` (needed for the cancellation step), derives the C2 form
  `nonneg(sub(sum_re², d·sum_im²))`. Located ~line 15240 of dyn_tower_lemmas.rs.

  The 7 implementation steps:
  1. Call `c2c3_ab_linear` → `nonneg(sub(a1·b2, b1·a2))`
  2. Distributive identity: prove `eqv(sub(sum_re·neg(b1), neg(sum_im)·a1), sub(a1·b2, b1·a2))`
     via repeated `neg_mul_left/right`, `mul_distributes_left`, `mul_commutative`,
     `add_exchange`, `add_inverse_right`, `add_zero_*`. Transfer nonneg via
     `nonneg_fuel_congruence`.
  3. `square_le_square_fuel(neg(sum_im)·a1, sum_re·neg(b1), f)` →
     `nonneg(sub((sum_re·neg(b1))², (neg(sum_im)·a1)²))`.
  4. Simplify the squares via `square_of_product` + `neg_mul_neg`:
     `(sum_re·neg(b1))² ≡ sum_re²·b1²` and `(neg(sum_im)·a1)² ≡ sum_im²·a1²`.
     Apply `sub_congruence_both` to transfer nonneg → `nonneg(sub(sum_re²·b1², sum_im²·a1²))`.
  5. Scale C2 by sum_im² via `le_mul_nonneg_monotone_fuel(dbb1, aa1, sum_im_sq, f)` →
     `nonneg(sub(aa1·sum_im_sq, dbb1·sum_im_sq))`. Then commute to
     `nonneg(sub(sum_im_sq·aa1, sum_im_sq·dbb1))` via mul_commutative.
  6. Chain Step 4 + Step 5 via `lemma_sub_add_sub` (the algebraic identity
     `sub(A, B) + sub(B, C) ≡ sub(A, C)`) to get
     `nonneg(sub(sum_re²·b1², sum_im²·dbb1))`.
  7. Rewrite `sum_im²·dbb1 ≡ (d·sum_im²)·bb1` via mul_associative + mul_commutative
     + congruences. Then apply `le_mul_cancel_pos_fuel(dsisq, sum_re_sq, bb1, f)`
     using `nonneg(bb1)` (square_nonneg) and `!is_zero(bb1)` derived from
     `!is_zero(b1)` via `mul_cancel_zero(b1, b1)` (integral domain).
  Result: `nonneg(sub(sum_re², d·sum_im²))` ✓

- **TODO**: `lemma_dts_c2c3_neg_norm_bound` — Case 3 mirror. Same
  structure as `c2c3_norm_bound` but cancel by `b2²` instead of `b1²`.
  Expected size: ~1500 lines (similar plumbing).
  Strategy: copy `c2c3_norm_bound` and:
  - Swap `b1`↔`b2` in the cancellation side
  - Adjust the distributive identity in Step 2 (the linear cross-term will
    still be `a1·b2 - b1·a2` from `c2c3_ab_linear`, but the distribution
    will use `neg(sum_re)` and `sum_im` instead of `sum_re` and `neg(sum_im)`)
  - Cancel `bb2` using `!is_zero(b2)` from C3
  - Final goal: `nonneg(sub(d·sum_im², sum_re²))` (the C3 neg-norm form)

- **TODO**: Wire C2+C3 / C3+C2 dispatch in `nonneg_add_remaining`. Replace
  the current TODO branch (~line 15387) with:
  ```rust
  //  C2+C3 or C3+C2.
  lemma_dts_nonneg_or_neg_nonneg_fuel(sum_re, f);
  lemma_dts_nonneg_or_neg_nonneg_fuel(sum_im, f);
  if dts_nonneg_fuel(sum_re, f) && dts_nonneg_fuel(sum_im, f) {
      // Case 1: trivially C1
      return;
  }
  if dts_nonneg_fuel(sum_re, f) {
      // Case 2: sum_re ≥ 0, sum_im < 0
      // Establish !is_zero(b1) (for c2c3_norm_bound's precondition)
      // — comes from C2's b_neg condition
      lemma_dts_c2c3_norm_bound(a1_c2_side, b1_c2_side, a2_c3_side, b2_c3_side, dd, f);
      lemma_dts_nonneg_conclude_re_fuel(sum_re, sum_im, dd, f);
      return;
  }
  if dts_nonneg_fuel(sum_im, f) {
      // Case 3: sum_re < 0, sum_im ≥ 0
      lemma_dts_c2c3_neg_norm_bound(...);
      lemma_dts_nonneg_conclude_im_fuel(...);
      return;
  }
  // Case 4: both negative — derive contradiction (see Case 4 sketch above)
  ```
  Note: the dispatch needs to handle BOTH C2+C3 (a1_nn ∧ !b1_nn ∧ !a2_nn ∧ b2_nn)
  and C3+C2 (!a1_nn ∧ b1_nn ∧ a2_nn ∧ !b2_nn) — same code with arguments swapped
  to put the C2 side first.

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
| `lemma_dts_le_mul_cancel_pos_fuel` | ~10230 | ✅ VERIFIED (session 9) |
| `lemma_dts_cauchy_cross_term_neg` | ~12010 | ✅ VERIFIED (session 8) |
| `lemma_dts_c2c2_norm_bound` | ~12283 | ✅ VERIFIED (session 7) |
| `lemma_dts_c3c3_neg_norm_bound` | ~12654 | ✅ VERIFIED (session 8) |
| `lemma_dts_norm_sum_decomposition` | ~13325 | ✅ VERIFIED (session 7) |
| `lemma_dts_c1c3_neg_norm_bound` | ~13543 | ✅ VERIFIED (session 8) |
| `lemma_dts_c2c3_ab_linear` | ~14498 | **✅ VERIFIED (session 9b)** |
| `lemma_dts_c2c3_norm_bound` | ~15240 | **✅ VERIFIED (session 9b)** |
| `lemma_dts_c2c3_neg_norm_bound` | ~16719 | **✅ VERIFIED (session 10)** |
| `lemma_dts_c2c3_iszero_sum_im_implies_nonneg_sum_re` | ~18395 | **✅ VERIFIED (session 10)** |
| `lemma_dts_c2c3_case4_contradiction` | ~18797 | **✅ VERIFIED (session 10)** |
| `lemma_dts_norm_transfer` | ~19170 | **✅ VERIFIED (session 10)** |
| `lemma_dts_nonneg_add_remaining` | ~19535 | **✅ VERIFIED (session 10)** |
| `lemma_dts_nonneg_add_closed_fuel` | ~20005 | **✅ VERIFIED** |

## Decreases Hierarchy (Updated for Session 9b)

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
| `le_mul_cancel_pos` | (fuel, 3nat) | VERIFIED (session 9) |
| `cauchy_cross_term` | (fuel, 4nat) | VERIFIED (session 7) |
| `cauchy_cross_term_neg` | (fuel, 4nat) | VERIFIED (session 8) |
| `c2c3_ab_linear` | (fuel, 4nat) | **VERIFIED (session 9b)** |
| `c2c2_norm_bound` | (fuel, 5nat) | VERIFIED (session 7) |
| `c3c3_neg_norm_bound` | (fuel, 5nat) | VERIFIED (session 8) |
| `c2c3_norm_bound` | (fuel, 6nat) | **VERIFIED (session 9b)** |
| `c2c3_neg_norm_bound` | (fuel, 6nat) | **VERIFIED (session 10)** |
| `iszero_sum_im_implies_nonneg_sum_re` | (fuel, 4nat) | **VERIFIED (session 10)** |
| `case4_contradiction` | (fuel, 5nat) | **VERIFIED (session 10)** |
| `norm_transfer` | (fuel, 0nat) | **VERIFIED (session 10)** |
| `nonneg_add_remaining` | (fuel, 8nat) | **✅ VERIFIED (session 10)** |
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

12. **`mul_cancel_zero` for `!is_zero(b·b)` from `!is_zero(b)`** (session 9b):
    `lemma_dts_mul_cancel_zero(b, b)` takes `is_zero(b·b)` ∧ `!is_zero(b)`
    and derives `is_zero(b)` (contradiction). Use inside an
    `if dts_is_zero(b·b) { ... }` branch to give Z3 the contradiction.
    Critical for the cancellation step in `c2c3_norm_bound`.

13. **Long proofs (>1000 lines) lose track of sr facts** (session 9b): Z3's
    context gets polluted, so even sr facts that were established earlier
    may need to be REBUILT explicitly closer to the call site. When you
    see "precondition not satisfied" on a sr precondition that you "know"
    you established, rebuild the chain with explicit `same_radicand_*`
    calls a few lines before the failing call.

14. **For `mul_closed(x, x)` etc., reflexive sr is needed** (session 9b):
    `mul_closed(a, a)` requires `sr(a, a)` which is reflexive — but Z3
    won't automatically derive it. Always call `same_radicand_reflexive(a)`
    before squared `mul_closed` calls.

15. **`mul_congruence_left/right` need both eqv AND sr** (session 9b):
    `mul_congruence_right(a, b, c)` requires `eqv(a, b)` AND `sr(a, b)`.
    So building eqv via `mul_commutative` etc. is not enough — also need
    explicit sr chain between the two equivalent expressions.

16. **Z3 can't unfold Ext spec fn in long functions** (session 10): In a 500+
    line function, Z3 may not unfold `dts_nonneg_fuel(Ext(Box::new(a), ...), f+1)`
    to derive that `a_nn || b_nn`. Even in clean-context helpers, Box deref
    matching can fail. Fix: add a caller-side precondition that explicitly
    states the consequence (e.g., `!(a1_nn && a2_nn && (b1_nn || b2_nn))`),
    and extract boolean exhaustion to a tiny helper with only bool parameters.

17. **C3+C2 congruence via norm_transfer** (session 10): For symmetric
    dispatch (C3+C2 mirrors C2+C3), call helpers with swapped args then
    use a dedicated `norm_transfer` helper to convert `nonneg(sub(X'², d·Y'²))`
    to `nonneg(sub(X², d·Y²))` given `eqv(X', X)` and `eqv(Y', Y)`.
    Avoids duplicating ~1500 lines of proof for the symmetric case.

## Cancellation-by-b1² strategy: implementation pattern

The `c2c3_norm_bound` proof revealed a useful design pattern for
DTS proofs that need to "divide" by something (which DTS can't do directly):

1. **State the goal in scaled form**: Multiply the desired inequality by
   the cancellation factor squared. E.g., to prove `sum_re² ≥ d·sum_im²`,
   prove `sum_re²·b1² ≥ d·sum_im²·b1²` instead.

2. **Chain the scaled facts** using `le_mul_nonneg_monotone_fuel` and
   `sub_add_sub`. Each scaling preserves the squared form.

3. **Cancel at the end** using `lemma_dts_le_mul_cancel_pos_fuel`, which
   requires `nonneg(c)` (square_nonneg) and `!is_zero(c)`. The `!is_zero`
   is the trickiest part — you need to derive it from problem-specific
   conditions (e.g., `!is_zero(b1)` from C2's `b_neg`).

4. **Use the `mul_cancel_zero` integral domain trick** for `!is_zero(b·b)`:
   inside `if dts_is_zero(b·b) { lemma_dts_mul_cancel_zero(b, b); }` —
   the if-branch contradiction gives Z3 `!is_zero(b·b)` outside.

This pattern should generalize to other DTS proofs that need division
or cancellation.
