# DTS nonneg_mul & nonneg_add — Status & Handoff (2026-04-09, sessions 4-6)

## Current State: 131 verified, 1 error

The nonneg_mul mutual recursion group is **fully verified**. The remaining error is in `lemma_dts_nonneg_add_remaining` which has 3 unproved return paths (C2 norm bound, C3 neg_norm bound, both-neg contradiction).

`nonneg_add_closed_fuel` itself verifies (it trusts the helper's postcondition via mutual recursion). The 9 `axiom_non_square` errors are pre-existing and unrelated.

## What Was Done

### nonneg_mul_remaining: VERIFIED (sessions 4-5)

Created two clean-context helpers to bypass Z3 context pollution in the 800-line `nonneg_mul_remaining` function:

1. **`lemma_nonneg_mul_neg_im_path`** (~370 lines, rlimit 500, decreases (f, 8nat)):
   Handles the `!nonneg(im_val)` path. Dispatches on norm signs: pos norms → reverse_cauchy → conclude_re; neg norms → neg_norms_nonneg_re_val → conclude_re; mixed norms → mixed_norms_nonneg_im_val → contradiction with !nonneg(im).

2. **`lemma_nonneg_mul_nonneg_im_path`** (~335 lines, rlimit 500, decreases (f, 8nat)):
   Handles the `nonneg(im_val)` path (all norm cases). Pos norms → reverse_cauchy + nonneg_mul(nx,ny) → conclude_re. Neg norms → neg_norms + neg_mul_neg → conclude_re. Mixed norms → neg_mul chain → nonneg(neg(nx*ny)) → conclude_im_via_neg_norm.

The parent `nonneg_mul_remaining` was reduced from ~800 lines of inline code to a simple `if !im_check { neg_im_path(); return; } else { nonneg_im_path(); return; }`.

### nonneg_add_closed_fuel: Skeleton in place (session 6)

Created `lemma_dts_nonneg_add_remaining` (~100 lines) that dispatches on component signs:
- **Case 1 (C1)**: Both sum_re=a1+a2 and sum_im=b1+b2 nonneg → VERIFIED
- **Case 2 (C2)**: sum_re nonneg, sum_im neg → needs norm bound (WIP)
- **Case 3 (C3)**: sum_re neg, sum_im nonneg → needs neg_norm bound (WIP)
- **Case 4**: Both neg → needs contradiction proof (WIP)

### Algebraic Building Blocks (session 6)

1. **`lemma_dts_square_of_sum`** (~150 lines, VERIFIED):
   Proves `(a+b)² ≡ add(add(a², b²), add(ab, ab))` via distributivity twice + 6-step additive rearrangement using associativity/commutativity.

2. **`lemma_dts_norm_sum_decomposition`** (~140 lines, WIP):
   Proves `N(x+y) ≡ N(x) + N(y) + 2*cross` where cross = sub(a1*a2, dd*b1*b2).
   Uses square_of_sum + distribute dd. Missing: mul_congruence chain + sub_add_sub rearrangement.

## Remaining Work: nonneg_add_remaining

### Step 1: Complete `norm_sum_decomposition` (~50 lines)

The skeleton has the distribute calls but the congruence chain is incomplete.

**What needs to happen:**
1. Fix `mul_congruence_right(dd, ...)` — either fix sr preconditions or use `mul_distributes_left` results directly
2. Chain: dd*(b1+b2)² ≡ dd*square_of_sum_RHS ≡ add(add(dd*b1², dd*b2²), add(dd*b1*b2, dd*b1*b2))
   via mul_congruence + distributes_left (twice)
3. Apply sub_congruence on both (a1+a2)² and dd*(b1+b2)² results
4. Rearrange sub(add(A,C), add(B,D)) ≡ add(sub(A,B), sub(C,D)) using the identity from `verus-geometry/src/circle_line.rs:213` (sub_add_sub 4-arg version)
5. Further rearrange sub(add(a1²,a2²), add(dd*b1²,dd*b2²)) ≡ add(sub(a1²,dd*b1²), sub(a2²,dd*b2²)) using the same identity

**Key functions:**
- `lemma_dts_mul_congruence_right(a, b, c)`: eqv(b,c) → eqv(mul(a,b), mul(a,c)). Requires sr(a,b).
- `lemma_sub_add_sub(a, b, c, d)` from verus-geometry: (a-b)+(c-d) ≡ (a+c)-(b+d)
- `lemma_dts_sub_congruence(a, b, c, d)`: eqv(a,b) ∧ eqv(c,d) → eqv(sub(a,c), sub(b,d)). (Check if this exists; otherwise build from add_congruence + neg_congruence.)

### Step 2: Cauchy Cross-Term Lemma (~100-150 lines, new function)

Create `lemma_dts_cauchy_cross_term` that proves the cross-term sign from norm bounds.

**For positive norms (C2+C2 and similar):**
Given nonneg(sub(a1², dd*b1²)) and nonneg(sub(a2², dd*b2²)) and nonneg(a1*a2) and nonneg(dd*b1*b2), derive nonneg(sub(a1*a2, dd*b1*b2)).

**Proof approach:**
1. `le_mul_nonneg_monotone(dd*b1², a1², a2²)`:
   nonneg(sub(a1², dd*b1²)) ∧ nonneg(a2²) → nonneg(sub(a1²*a2², dd*b1²*a2²))
2. `le_mul_nonneg_monotone(dd*b2², a2², dd*b1²)`:
   nonneg(sub(a2², dd*b2²)) ∧ nonneg(dd*b1²) → nonneg(sub(a2²*dd*b1², dd*b2²*dd*b1²))
3. `sub_add_sub` (telescoping): sub(a1²*a2², dd*b1²*a2²) + sub(dd*b1²*a2², dd²*b1²*b2²) ≡ sub(a1²*a2², dd²*b1²*b2²)
   Note: middle terms need mul_commutative to match: dd*b1²*a2² ≡ a2²*dd*b1²
4. Ring identities: (a1*a2)² ≡ a1²*a2² and (dd*b1*b2)² ≡ dd²*b1²*b2² (need mul_associative/commutative chains)
5. `square_le_implies_le(dd*b1*b2, a1*a2, f)`: nonneg(a1*a2) ∧ nonneg(dd*b1*b2) ∧ (a1*a2)²≥(dd*b1*b2)² → nonneg(sub(a1*a2, dd*b1*b2))

**For negative norms (C3+C3):** Symmetric: swap a and b roles.

**For mixed signs (one nonneg, one neg cross-term):** If nonneg(a1*a2) and nonneg(neg(dd*b1*b2)): trivially nonneg(sub(a1*a2, dd*b1*b2)) via nonneg_add.

**Existing helpers to reuse:**
- `le_mul_nonneg_monotone_fuel` at (fuel, 2nat)
- `square_le_implies_le_fuel` at (fuel, 3nat)
- `sub_add_sub` (algebraic, no fuel) — telescoping version
- `square_nonneg` (standalone)
- `nonneg_mul_closed_fuel` at (fuel, 0nat)

### Step 3: Wire into add_remaining (~50 lines per case)

**Case 2 (C2: sum_re nonneg, sum_im neg):**
```
// Call norm_sum_decomposition to get N(sum) ≡ N(x)+N(y)+2*cross
// Establish nonneg of each term (N(x) from factor nonneg, N(y) from factor nonneg, cross from Cauchy)
// nonneg_add three times → nonneg(N(x)+N(y)+2*cross)
// nonneg_fuel_congruence: N(sum) ≡ sum → nonneg(N(sum))
// conclude_re(sum_re, sum_im, dd, f)
return;
```

**Case 3 (C3: sum_im nonneg, sum_re neg):**
Same structure but with neg norms:
```
// neg(N(sum)) ≡ neg(N(x))+neg(N(y))+2*neg(cross) via neg_congruence on decomposition
// Each term nonneg (neg norms from C3, neg_cross from Cauchy)
// nonneg_add → nonneg(neg(N(sum)))
// !is_zero(sum_im) from: !nonneg(sum_im) would give sum_im=0 → nonneg, contradicting !nonneg(sum_re) + sum nonneg
// C3 conditions: nonneg(sum_im) ∧ !is_zero(sum_im) ∧ nonneg(neg(norm))
return;
```

**Case 4 (both neg: contradiction):**
Derive false from nonneg(x) ∧ nonneg(y) ∧ !nonneg(sum_re) ∧ !nonneg(sum_im).
Approach: case-split on C1/C2/C3 of each factor. For every combination, at least one of sum_re or sum_im must be nonneg (C1/C2 have a≥0 → sum_re≥0 if both C1/C2; C3 has b>0 → sum_im>0 if both have b≥0). The only tricky case is C2+C3 with b1<0, b2>0, |b1|>b2 AND a1+a2<0. But a1≥0 from C2 and a2 might be neg from C3, so a1+a2<0 means |a2|>a1. Combined with both sum components neg, this contradicts x+y≥0 (both terms of sum negative). (~30-50 lines of case analysis)

**Termination:** Remove the `nonneg_mul_closed_fuel(x_ext, y_ext, f+1)` call (termination error). All calls must be at fuel f with decreases (f, X) for X ≤ 7.

## Key Termination Constraint

The helper `lemma_dts_nonneg_add_remaining` is at `decreases (f, 8nat)` where f = fuel-1 from the caller `nonneg_add_closed_fuel` at `(fuel, 0nat)`.

**Can call at fuel f:** nonneg_mul_closed (f,0), nonneg_add_closed (f,0), le_mul_nonneg_monotone (f,2), square_le_implies_le (f,3), nonneg_or_neg (f,2), nonneg_re_from_nonneg_norm (f,2), all lower-level helpers.

**CANNOT call at fuel f+1:** Would need (f+1, X) < (f, 8) which fails since f+1 > f. Must work with component-level nonneg facts (nonneg(a1,f), nonneg(b1,f), nonneg(norm_x,f)) extracted from nonneg(Ext, f+1).

## Decreases Hierarchy (Current)

| Function | Decreases | Status |
|----------|-----------|--------|
| nonneg_mul_closed | (fuel, 0) | VERIFIED |
| nonneg_add_closed | (fuel, 0) | VERIFIED (trusts helper) |
| cauchy_schwarz_step | (fuel, 1) | VERIFIED |
| le_antisymmetric | (fuel, 1) | VERIFIED |
| nonneg_fuel_congruence | (fuel, 2) | VERIFIED |
| nonneg_or_neg | (fuel, 2) | VERIFIED |
| le_mul_nonneg_monotone | (fuel, 2) | VERIFIED |
| nonneg_re_from_nonneg_norm | (fuel, 2) | VERIFIED |
| nonneg_component_from_ext | (fuel, 3) | VERIFIED |
| square_le_implies_le | (fuel, 3) | VERIFIED |
| reverse_cauchy_nonneg_re | (fuel, 5) | VERIFIED |
| neg_norms_nonneg_re_val | (fuel, 6) | VERIFIED |
| mixed_norms_nonneg_im_val | (fuel, 6) | VERIFIED |
| error_b_dispatch | (fuel, 7) | VERIFIED |
| **nonneg_mul_neg_im_path** | **(fuel, 8)** | VERIFIED |
| **nonneg_mul_nonneg_im_path** | **(fuel, 8)** | VERIFIED |
| **nonneg_add_remaining** | **(fuel, 8)** | **3 errors** |
| nonneg_mul_remaining | (fuel, 9) | VERIFIED |

## File Locations

All in `verus-quadratic-extension/src/dyn_tower_lemmas.rs`:

| Function | ~Line | Status |
|----------|-------|--------|
| square_of_sum | ~10821 | VERIFIED |
| norm_sum_decomposition | ~10969 | WIP |
| nonneg_add_remaining | ~11113 | 3 errors |
| nonneg_add_closed_fuel | ~11225 | VERIFIED |
| c1c2_norm_bound | ~10301 | VERIFIED |
| le_mul_nonneg_monotone_fuel | ~10129 | VERIFIED |
| square_le_implies_le_fuel | ~1375 | VERIFIED |

## Z3 Context Pollution Lessons (Updated)

1. **Let-binding connections lost over 530+ lines.** Solution: clean-context helpers.
2. **same_radicand chains lost over distance.** Solution: re-establish sr chains immediately before the call that needs them.
3. **rlimit increases don't help context pollution.** The issue is Z3 losing facts, not running out of time.
4. **Argument ordering for add_congruence_left/right matters.** `right(c, a, b)`: eqv(a,b) → eqv(add(c,a), add(c,b)). The "c" is the FIXED part.
5. **DTS add_associative/add_commutative have NO sr preconditions** — much simpler than mul versions. Use for additive rearrangements.
6. **DynTowerSpec does NOT implement Ring** — only AdditiveGroup. Can't use generic ring lemmas. Must use DTS-specific mul_distributes_left, mul_commutative, etc. (which need wf+sr).
7. **Termination: can't call mutual-recursion functions at higher fuel.** At (f, 8nat), can't call anything at fuel f+1. Must work with components at fuel f.
