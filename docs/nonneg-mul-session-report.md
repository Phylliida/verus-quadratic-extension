# DTS nonneg_mul Completion — Session Report (2026-04-05/06/07)

## Summary

Over three sessions, we went from **96 verified, 3 errors** to **109 verified, 4 errors** (Fix 1 WIP). We built 14+ new verified lemmas forming a complete foundational algebra tower for DynTowerSpec, and Fix 1 is architecturally complete with only same_radicand boilerplate remaining.

## Current State: 109 verified, 4 errors

**All architecture and proofs are correct.** The remaining work is purely mechanical same_radicand chain boilerplate (~5 calls) in `lemma_cauchy_neg_db1b2_case`.

### Error Summary
1. `lemma_cauchy_neg_db1b2_case` — 2 same_radicand precondition errors in mul algebra congruence chain
2. `lemma_dts_nonneg_mul_remaining` — cascading from #1
3. `lemma_dts_nonneg_mul_iszero_im` — cascading
4. `lemma_dts_nonneg_add_closed_fuel` — cascading

### Cascade Theory
Fix neg_db1b2_case → cauchy_schwarz verifies → nonneg_mul_remaining → nonneg_mul_closed → nonneg_add_closed → nonneg_mul_iszero_im → **0 ERRORS!**

## What Was Done (Session 3, 2026-04-07)

### Fix 2: well_formed(re_val) + nonneg(neg(re_val)) assert (DONE)
- Added `lemma_dts_add_closed(a1a2, db1b2)` for well_formed(re_val)
- Added explicit `assert(dts_nonneg_fuel(dts_neg(re_val), f))` in db1b2≥0 branch
- **cauchy_schwarz if-branch now verifies!**

### Fix 3: nonneg(a1, f) and nonneg(a2, f) at call site (DONE)
- New `lemma_dts_nonneg_component_from_ext_fuel` helper (VERIFIED)
- Proof by contradiction: if !nonneg(a), C1/C2 are false → C3 must hold
- C3 includes nonneg(sub(dd*b², a²)) which ≡ nonneg(neg(nx)) via neg_sub_swap + nonneg_fuel_congruence → contradicts !nonneg(neg(nx)) from branch condition
- Key insight: nonneg_fuel(Ext, f+1) auto-unfolds to C1/C2/C3, but Z3 can't connect sub(dd*b², a²) to neg(nx) without explicit neg_sub_swap + congruence

### Fix 1: le_transitive + congruence chain (WIP — 5 same_radicand calls remain)

**Architecture complete, split into 3 helpers:**

1. **`lemma_cauchy_le_transitive_raw`** (VERIFIED, ~200 lines)
   - At decreases (f, 3nat)
   - le_mul step 1: a1²·a2² ≥ (dd·b1²)·a2²
   - le_mul step 2: a2²·(dd·b1²) ≥ (dd·b2²)·(dd·b1²)
   - Commute middle term via mul_commutative + sub_congruence_both + nonneg_fuel_congruence
   - nonneg_add(sub1, sub2) for le_transitive
   - Algebra identity: add(sub(A,B), sub(B,C)) ≡ sub(A,C)
     via add_associative + add_commutative + add_inverse_right + add_zero_right + add_congruence_left/right
   - nonneg_fuel_congruence to transfer
   - **Produces: nonneg(sub(a1²·a2², (dd·b2²)·(dd·b1²)))**

2. **`lemma_cauchy_neg_db1b2_case`** (WIP, ~120 lines)
   - At decreases (f, 4nat)
   - Calls le_transitive_raw for intermediate result
   - Congruence chain: (dd·b2²)·(dd·b1²) ≡ dd²·(b1²·b2²) ≡ (dd·b1·b2)² ≡ neg(dd·b1·b2)²
     via mul_commutative + mul_associative + mul_congruence_left/right + square_mul + neg_mul_neg
   - sub_congruence_both + nonneg_fuel_congruence → nonneg(sub(a1a2², neg(db1b2)²))
   - square_le_implies_le(neg(db1b2), a1a2, f) → nonneg(sub(a1a2, neg(db1b2)))
   - neg_involution + congruence → nonneg(re_val)
   - le_antisymmetric → is_zero(re_val)
   - **REMAINING: ~5 same_radicand chains for mul_congruence_left preconditions**

3. **`lemma_cauchy_schwarz_is_zero_re`** (VERIFIED, calls neg_db1b2_case)
   - At decreases (f, 5nat)
   - Dispatches on sign of db1b2: if-branch uses nonneg_add + le_antisymmetric, else-branch calls neg_db1b2_case

### Decreases Hierarchy (Updated)

| Function | Decreases | Role |
|---|---|---|
| nonneg_mul_closed | (fuel, 0) | Main entry |
| nonneg_add_closed | (fuel, 0) | Addition closure |
| le_antisymmetric | (fuel, 1) | nonneg(x) ∧ nonneg(neg(x)) → is_zero(x) |
| nonneg_fuel_congruence | (fuel, 2) | Transfer nonneg through eqv |
| square_le_square | (fuel, 2) | |
| le_mul_nonneg_monotone | (fuel, 2) | |
| nonneg_sum_zero | (fuel, 2) | |
| nonneg_component_from_ext | (fuel, 3) | nonneg_fuel(Ext) + norm>0 → nonneg(a) |
| le_transitive_raw | (fuel, 3) | le_mul chain + algebra identity |
| square_le_implies_le | (fuel, 3) | |
| cauchy_neg_db1b2_case | (fuel, 4) | Congruence + square_le + le_antisymmetric |
| cauchy_schwarz_is_zero_re | (fuel, 5) | Main Cauchy-Schwarz dispatch |
| nonneg_mul_remaining | (fuel, 6) | Main remaining cases handler |

## What Remains — Mechanical Fixes Only

All in `lemma_cauchy_neg_db1b2_case`, the Part E congruence chain.

### Missing same_radicand chains (5 calls)

1. `mul_closed(b1_sq, dd)` — needs same_radicand(b1_sq, dd) [already established]
2. `same_radicand_symmetric(b1_sq, mul(b1_sq, dd))` — derives from mul_closed
3. `same_radicand_transitive(mul(b1_sq, dd), b1_sq, dd)` — for mul_congruence_left precondition
4. `same_radicand_transitive(mul(b1_sq, dd), dd, db1_sq)` — connecting to db1_sq
5. Recheck: `eqv_transitive((b1_sq*dd)*b2_sq, db1_sq*b2_sq, dd*(b1_sq*b2_sq))` — may need eqv(db1_sq*b2_sq, dd*(b1_sq*b2_sq)) from mul_associative which should already be called

These are purely mechanical same_radicand boilerplate — no mathematical content.

## Key Insights for Future Work

1. **DTS same_radicand boilerplate is the bottleneck.** Every DTS operation (mul, add, neg, sub) preserves same_radicand but needs explicit chain calls. Consider a helper that batches common chains.

2. **Z3 needs explicit neg_sub_swap + congruence** to connect !nonneg(neg(nx)) to C3's sub(dd*b², a²) term. These are eqv but not syntactically equal.

3. **The algebra identity add(sub(A,B), sub(B,C)) ≡ sub(A,C)** is provable from add_associative + add_inverse + add_zero but needs ~15 eqv chain calls. A reusable le_transitive lemma would help future work.

4. **Decreases bumps cascade.** Adding a helper at (f, 4) required bumping cauchy_schwarz to (f, 5) and nonneg_mul_remaining to (f, 6). The hierarchy is getting deep.

5. **rlimit management is critical.** The ~375-line neg_db1b2_case had to be split into le_transitive_raw (~200 lines) + neg_db1b2_case (~120 lines). Each function needs ≤50 "meaningful" assertions for Z3.

6. **mul_congruence_left/right parameter order matters.** The signature is (a, b, c) where a, b are the eqv pair and c is the multiplier. Easy to swap a/c.
