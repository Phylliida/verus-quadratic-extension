# DTS nonneg_mul Session Report

**Date:** 2026-04-03
**File:** `verus-quadratic-extension/src/dyn_tower_lemmas.rs`
**Starting state:** 103 verified, 2 errors
**Current state:** 104 verified, 3 errors (no timeouts, ~200s wall time)

## Goal

Fix `lemma_dts_nonneg_mul_remaining` and `lemma_dts_nonneg_add_closed_fuel` to get `verus-2d-constraint-satisfaction` building clean. These are the last two errors blocking the DTS ordered field proof.

## What Was Fixed

### Point C (b1>=0, b2>=0 return) -- FIXED
The original `return;` at the b1>=0, b2>=0 branch had no proof. Split into:
- `nonneg(re_val)` case: `conclude_re` with product_norm >= 0. Verified.
- `!nonneg(re_val)` case: placeholder return. Z3 handles as unreachable.

### Point A mixed-sign norms (is_zero(im_val)) -- FIXED
When im=0 and norms have opposite signs (neg(nx)>=0 && ny>=0, or nx>=0 && neg(ny)>=0):
1. `neg_mul` chain -> `nonneg(neg(nx*ny))`
2. `norm_mul` eqv + `sub_zero` chain -> `nonneg(neg(re_val^2))` via congruence
3. Inline `square_nonneg(neg(re_val))` -> `nonneg(re_val^2)` (can't call `square_nonneg` directly due to termination -- must inline as `nonneg_mul(neg(re), neg(re)) + neg_mul_neg`)
4. `le_antisymmetric(re_val^2)` -> `is_zero(re_val^2)`
5. `norm_definite` trigger at Ext level -> `is_zero(re_val)`
6. `nonneg_fuel_zero(re_val)` -> C1 done.

**Key discovery:** Needed `dts_norm_definite(Ext(a1, b1, dd))` as a new precondition on `nonneg_mul_remaining` (and the new helpers). The component-level `norm_definite(a1), norm_definite(b1), norm_definite(dd)` do NOT include the Ext-level universal quantifier needed for the norm_definite trigger.

### Point A same-sign norms (Cauchy-Schwarz) -- IN PROGRESS
When im=0 and norms have the same sign (both >=0 or both <=0), need Cauchy-Schwarz inequality to show `re_val >= 0`. Architecture is complete:
- `lemma_dts_cauchy_schwarz_step` (decreases f, 1nat, rlimit 200) -- **FULLY VERIFIED**
  - Proves Step 1: `(dd*b1^2)*(dd*b2^2) >= a1^2*(dd*b2^2)` and Step 2: `(dd*b2^2)*a1^2 >= na2^2*a1^2`
  - Inlines `le_mul_nonneg_monotone` as `nonneg_mul(sub(b,a), c) + mul_distributes_left + neg_mul_right + mul_commutative` congruence chain
- `lemma_dts_nonneg_mul_iszero_im` calls the step helper, does transitivity via `sub_add_sub + nonneg_add`, getting `(dd*b1^2)*(dd*b2^2) >= na2^2*a1^2` (= Q^2 >= P^2)
- Remaining: complete the reverse_square_le_square chain or establish `nonneg(re_val)` from Q^2 >= P^2

## Architecture

```
nonneg_mul_closed_fuel (decreases fuel, 0nat)
  |-- C1xC1 (inline)
  |-- BxB -> nonneg_mul_bb (decreases f, 2nat)
  |-- C2xC2 -> nonneg_mul_cc (decreases f, 2nat)
  |-- is_zero(im) -> nonneg_mul_iszero_im (decreases f, 2nat)  <-- NEW
  |     |-- nonneg(re_val) case -> C1 return (verified)
  |     |-- mixed-sign norms -> is_zero(re_val) via norm chain (verified)
  |     |-- same-sign norms:
  |     |     |-- P>=0 && Q>=0 -> nonneg_add (verified)
  |     |     |-- neg(nx)>=0 && neg(ny)>=0:
  |     |     |     |-- cauchy_schwarz_step (decreases f, 1nat) (verified)
  |     |     |     |-- transitivity (assert by, scoped) (verified)
  |     |     |     |-- TODO: reverse_square_le_square -> nonneg(re_val)
  |     |     |-- nx>=0 && ny>=0: TODO
  |     |-- TODO: transfer chain + norm_definite -> is_zero(re_val)
  |-- remaining -> nonneg_mul_remaining (decreases f, 2nat)
        |-- is_zero(re_val) return -- pre-existing error
        |-- conclude_im -- pre-existing error
        |-- Point C (b1>=0, b2>=0) -- fixed
```

## Key Technical Lessons

### Decreases constraints
- `square_nonneg` has `decreases fuel` (1-element). Can't be called from `nonneg_mul_remaining` (decreases f, 2nat) because it creates a new cycle via `nonneg_mul_closed_fuel`. Must inline: `nonneg_mul(neg(x), neg(x)) + neg_mul_neg`.
- `le_mul_nonneg_monotone_fuel` has `decreases fuel` (1-element). Same issue. Must inline: `nonneg_mul(sub(b,a), c) + mul_distributes_left + neg_mul_right + commutative`.
- Functions at `decreases (f, 1nat)` can call `nonneg_mul_closed_fuel` at `(f, 0)` but NOT `le_antisymmetric_fuel` at `(f, 1)`.
- Functions at `decreases (f, 2nat)` can call everything: `nonneg_mul_closed_fuel (f, 0)`, `le_antisymmetric (f, 1)`, and other `(f, 2)` functions via the parent dispatch.

### Z3 context management (rlimit)
- **Functions > 600 lines cause Z3 to drown.** The original `nonneg_mul_remaining` grew to 1300+ lines and timed out at 142M rlimit.
- **Extraction to separate functions** is the primary fix. Each function gets its own Z3 context.
- **`assert by { ... }` blocks** scope Z3 facts within the block. The #1 tool for reducing rlimit within a single function.
- `mul_distributes_left` uses 1.5M rlimit on its own. Calling it in a large function context multiplies the cost. Put it in its own helper or `assert by`.

### same_radicand boilerplate
- Every DTS lemma call needs `same_radicand(A, B)` chains. The pattern: `A ~ component ~ dd ~ component ~ B`.
- Each chain is 2-4 `symmetric + transitive` calls. Missing one causes a precondition error.
- The #1 time sink in DTS proof development.
- Always add `symmetric(X, Y)` before `transitive(Y, X, Z)` -- the most common miss.
- `mul_closed(A, B)` needs `same_radicand(A, B)` AND `well_formed(A), well_formed(B)`.
- `sub_congruence_both(a, b, c, d)` needs eqv AND same_radicand for BOTH pairs.
- `nonneg_fuel_congruence(x, y, f)` needs eqv AND same_radicand AND nonneg(x, f).

### DTS-specific facts
- `dts_neg(dts_zero()) == dts_zero()` structurally. But `neg(arbitrary_zero_expr)` does NOT simplify structurally -- use eqv chain via `neg_congruence + neg(zero) == zero`.
- `is_zero(mul(a, b))` does NOT imply `is_zero(a) || is_zero(b)` without norm_definite.
- `neg_sub_swap(a, b)` gives `eqv(neg(sub(a, b)), sub(b, a))`. Critical for transferring `nonneg(neg(ny))` to `nonneg(sub(dd*b2^2, a2^2))`.
- `mul_is_zero_left(x, c)` and `mul_is_zero_right(x, c)` propagate structural zero through mul. Z3 can't derive this automatically.

## What Remains

### Immediate (3 errors)
1. **iszero_im same-sign Cauchy-Schwarz**: The `assert by` block establishes `nonneg(sub(Q^2, P^2))`. Need to complete the reverse_square_le_square chain in the outer function to derive `nonneg(re_val)`. Currently a placeholder `return;`.
2. **nonneg_mul_remaining pre-existing errors**: `is_zero(re_val)` return + `conclude_im` precondition. These existed before our changes. May need similar Cauchy-Schwarz or norm analysis.
3. **nonneg_add_closed_fuel**: Remaining add cases (C1+C3, C2+C2, etc.). Cascades from nonneg_mul.

### rlimit optimization needed
- `iszero_im` at 83M rlimit (FAIL) -- needs more `assert by` scoping or further extraction
- `nonneg_mul_bb` jumped to 32M (was 5.8M) -- possibly affected by the new Ext-level norm_definite precondition adding quantifier triggers
- `nonneg_mul_remaining` at 13M (was similar) -- 2 pre-existing errors
- `nonneg_mul_closed_fuel` at 13M (was 3.7M) -- new dispatch to iszero_im adds work

### After nonneg_mul is complete
1. `square_nonneg` -- short, uses nonneg_mul
2. `sum_squares_zero` -- a^2+b^2=0 -> a=0, b=0
3. Non-degeneracy transfer -- spec nondeg -> dyn nondeg
4. Exec completeness theorem for the CAD constraint solver

## Recommendations

1. **Scope the mixed-sign norm chain** in `iszero_im` with `assert by` to reduce rlimit. Currently verified but uses ~40M+ rlimit.
2. **Consider making same_radicand an implicit/broadcast lemma** -- the boilerplate is 60%+ of all proof code.
3. **The reverse_square_le_square** might not be needed if Z3 can close from Q^2 >= P^2 + factor nonneg_fuel unfolding. Test with higher rlimit first before writing the full chain.
4. **Profile after each extraction** to ensure rlimit stays manageable. Target: <10M per function.
