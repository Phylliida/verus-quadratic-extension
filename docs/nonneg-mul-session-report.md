# DTS nonneg_mul Completion — Session Report (2026-04-05/06)

## Summary

Over two sessions, we went from **96 verified, 3 errors** to **106 verified, 4 errors** (the 4th is a WIP helper). We built 10+ new verified lemmas forming a complete foundational algebra tower for DynTowerSpec, and are within ~3 mechanical fixes of **0 errors** — which would complete the `nonneg_mul_closed` proof and cascade-fix all remaining errors.

## What Was Done

### New Verified Lemmas (10+)

```
                    cauchy_schwarz_is_zero_re (WIP — 3 preconditions remain)
                          ↓ uses
              square_le_implies_le_fuel  ← VERIFIED
                    ↓ uses
          nonneg_sum_zero_implies_zero  ← VERIFIED
                    ↓ uses
            mul_cancel_zero (INTEGRAL DOMAIN)  ← VERIFIED
                    ↓ uses
              is_zero_norm  ← VERIFIED
                ↓       ↓ uses
    is_zero_mul_left   is_zero_mul_right  ← VERIFIED
         ↓       ↓ uses
  is_zero_add   is_zero_neg  ← VERIFIED
```

Plus: `transfer_neg_norm`, `conclude_im_via_neg_norm` — both VERIFIED.

### Structural Improvements
- Restructured same-sign norms: Point C proof properly scoped inside neg(nx)&&neg(ny) branch
- Added le_antisymmetric dispatch for is_zero(nx)/is_zero(ny) sub-cases
- Unified all mutual recursion decreases to 2-tuples `(fuel, Xnat)`
- Created `conclude_im_via_neg_norm` extracted helper for Z3 rlimit management

### Mutual Recursion Decreases Hierarchy

All functions in the nonneg_mul group now use 2-tuple decreases:

| Function | Decreases | Role |
|---|---|---|
| nonneg_mul_closed | (fuel, 0) | Main entry |
| nonneg_add_closed | (fuel, 0) | Addition closure |
| le_antisymmetric | (fuel, 1) | nonneg(x) ∧ nonneg(neg(x)) → is_zero(x) |
| square_le_square | (fuel, 2) | 0≤a≤b → a²≤b² |
| le_mul_nonneg_monotone | (fuel, 2) | a≤b ∧ c≥0 → ac≤bc |
| nonneg_sum_zero | (fuel, 2) | nonneg(a)+nonneg(b)+is_zero(a+b) → is_zero(a) |
| square_le_implies_le | (fuel, 3) | a²≤b² with 0≤a,0≤b → a≤b |
| cauchy_schwarz_is_zero_re | (f, 4) | Cauchy-Schwarz via le_mul chain |
| nonneg_mul_remaining | (f, 5) | Main remaining cases handler |

## What Remains — 3 Specific Fixes

All fixes are in `lemma_cauchy_schwarz_is_zero_re` in `dyn_tower_lemmas.rs` (~line 1575).

### Fix 1: Connect le_mul chain to square_le_implies_le precondition

**What:** `square_le_implies_le(neg(db1b2), a1a2, f)` needs `nonneg(sub(a1a2², neg(db1b2)²), f)`.

**Why it's blocked:** The le_mul chain gives results in terms of a1²*a2² and dd*b1²*dd*b2², but square_le needs (a1*a2)² and (dd*b1*b2)². The square_mul congruences are called but not connected via `sub_congruence_both` + `nonneg_fuel_congruence`.

**Available facts (already called):**
- `square_mul(a1, a2)`: eqv((a1*a2)², a1²*a2²)
- `square_mul(dd, mul(b1,b2))` + `square_mul(b1, b2)`: for (dd*b1*b2)²
- `neg_mul_neg(db1b2, db1b2)`: neg(x)² ≡ x²
- `difference_of_squares(db1b2, a1a2)`: P*S ≡ sub(a1a2², db1b2²)
- le_mul steps 1 & 2

**What to add (~15 lines):**
1. `mul_commutative(a2², dd*b1²)` to align middle terms of the two le_mul results
2. `nonneg_fuel_congruence` to transfer step 2 to commuted form
3. `nonneg_add` of the two sub results for le_transitive
4. Algebraic identity: sub(A,B)+sub(B,C) ≡ sub(A,C) via add_associative+add_inverse chains
5. `sub_congruence_both` to connect a1²*a2² ≡ (a1*a2)² and dd*b1²*dd*b2² ≡ (dd*b1*b2)²
6. `nonneg_fuel_congruence` for final transfer

### Fix 2: Assert neg(re_val) in db1b2≥0 branch

**What:** `le_antisymmetric(re_val, f)` needs `nonneg(neg(re_val), f)` which is in the requires but Z3 may need a hint.

**Fix:** Add `assert(dts_nonneg_fuel(dts_neg(re_val), f));` before le_antisymmetric.

### Fix 3: Provide nonneg(a1, f) and nonneg(a2, f) at call site

**What:** The caller `nonneg_mul_remaining` needs to provide `nonneg(a1, f)` and `nonneg(a2, f)`.

**Why derivable:** In the Cauchy-Schwarz path, nx>0 and ny>0. C3 requires nonneg(neg(nx)) which contradicts nx>0. So factors are C1/C2 → both have a_nn.

**Fix:** Before `cauchy_schwarz_is_zero_re` call in nonneg_mul_remaining:
```rust
lemma_dts_nonneg_or_neg_nonneg_fuel(a1, f);
lemma_dts_nonneg_or_neg_nonneg_fuel(a2, f);
// Z3: nx>0 rules out C3 (which needs neg(nx)≥0). So nonneg(a1) and nonneg(a2).
```

## Cascade Once Fixed

cauchy_schwarz verifies → nonneg_mul_remaining verifies → nonneg_mul_closed verifies → nonneg_add_closed cascade-fixes → nonneg_mul_iszero_im cascade-fixes → **0 ERRORS!**

## Key Insights for Future Work

1. **DTS doesn't implement Ring trait** — can't use Ring axioms on DTS values directly. T (base field) IS Ring. DTS mul_congruence/commutative need `same_radicand`.

2. **same_radicand(Ext, Rat(0)) = false** — can't use congruence with dts_zero() for Ext values. Workaround: structural induction or commutativity trick (is_zero_mul_left + mul_commutative + is_zero_congruence).

3. **Integral domain proof**: is_zero(mul(x,y)) → norm chain → induction on depth via norm_definite contrapositive. Key: norm reduces depth by 1.

4. **square_le_implies_le proof**: contradiction (assume b≤a → a²≥b² → a²=b²) + difference_of_squares ((a-b)(a+b)=0) + integral domain (is_zero(a-b) or a+b=0 → both zero).

5. **Extracted helpers critical for rlimit** in 600+ line functions. The conclude_im and cauchy_schwarz helpers have clean Z3 contexts.

6. **All mutual recursion decreases must use same tuple length.** Unified to 2-tuples.

7. **Cauchy-Schwarz via P*S**: P=re_val, S=sub(a1a2, db1b2). P*S ≡ (a1*a2)²-(dd*b1*b2)² via difference_of_squares. le_mul chain → nonneg(P*S). neg(P)*S ≥ 0 → le_antisymmetric → is_zero(P*S) → integral domain → is_zero(P). The db1b2≥0 case shortcuts to nonneg_add.
