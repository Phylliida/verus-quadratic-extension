# DTS nonneg_mul Completion — Session Report (2026-04-05/06/07/08)

## Summary

Over four sessions, we went from **96 verified, 3 errors** to **115 verified, 3 errors**. All new helpers are verified. The remaining errors are in `nonneg_mul_remaining` (mixed-norms b1*neg_b2 path) and pre-existing `iszero_im` / cascading `add_closed`.

## Current State: 115 verified, 3 errors

### Error Summary
1. `nonneg_mul_remaining` — 2 postcondition exits:
   - The `return;` at the TODO mixed-norms path (b1*neg_b2 section with !neg(nx)&&neg(ny))
   - End of function body (pre-existing uncovered path)
2. `nonneg_mul_iszero_im` — assertion failed (pre-existing)
3. `nonneg_add_closed_fuel` — cascading from nonneg_mul

### New Verified Helpers (Session 4)
1. **`lemma_dts_dd_sq_product_eqv`** (standalone, no fuel) — proves (dd*b1²)*(dd*b2²) ≡ (dd*b1*b2)²
2. **`lemma_cauchy_le_chain_neg_norms`** (f, 3nat) — le_mul chain for reversed direction (dd*bi² ≥ ai²)
3. **`lemma_cauchy_neg_a1a2_square_le`** (f, 4nat) — congruence + square_le_implies_le → nonneg(re_val)
4. **`lemma_cauchy_nonneg_re_dispatch`** (f, 6nat) — clean-context wrapper with nx/ny ghost params for Z3 context pollution

### What Was Fixed
- **Task A (neg(a1*a2) case)**: COMPLETE. The else branch in `cauchy_nonneg_re_from_neg_norms` now calls `le_chain_neg_norms` + `neg_a1a2_square_le` to prove nonneg(re_val) when a1*a2 < 0.
- **Task B (call site Z3 pollution)**: PARTIAL. The dispatch wrapper with ghost equality params (`nx == dts_sub(...)`) fixes the first call site (inside neg(nx)&&neg(ny) branch). The second call site (b1*neg_b2 section) can't use the wrapper because neg(nx)&&neg(ny) isn't guaranteed there.

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
| le_transitive_raw | (fuel, 3) | le_mul chain + algebra identity (norm ≥ 0) |
| le_chain_neg_norms | (fuel, 3) | le_mul chain reversed (norm ≤ 0) |
| square_le_implies_le | (fuel, 3) | |
| neg_db1b2_case | (fuel, 4) | Congruence + square_le + le_antisymmetric |
| neg_a1a2_square_le | (fuel, 4) | Congruence + square_le → nonneg(re_val) |
| cauchy_schwarz_is_zero_re | (fuel, 5) | Main Cauchy-Schwarz dispatch |
| cauchy_nonneg_re_from_neg_norms | (fuel, 5) | Both norms ≤ 0 → nonneg(re_val) |
| cauchy_nonneg_re_dispatch | (fuel, 6) | Clean-context wrapper for Z3 |
| nonneg_mul_remaining | (fuel, 7) | Main remaining cases handler |

## What Remains

### Mixed-norms b1*neg_b2 path
The TODO `return;` at the b1*neg_b2 section: when NOT(neg(nx)≥0 && neg(ny)≥0) but b1*neg_b2 ≥ 0 and !nonneg(a1*a2). Needs a different proof approach — either:
1. Show this path is unreachable (the neg(nx)&&neg(ny) + nx&&ny cases already returned)
2. Use a norm-product approach: P*S = re_val * s_val where S = a1*a2 + dd*b1*|b2|

### iszero_im assertion
Pre-existing error in the Cauchy-Schwarz step of `nonneg_mul_iszero_im`.

### Key Z3 Technique Discovered
**Ghost equality params**: When Z3 can't connect let-bindings to expanded forms in large functions, use a wrapper with ghost parameters:
```
proof fn wrapper(..., nx: T)
    requires nx == expanded_form(...), dts_nonneg_fuel(dts_neg(nx), f), ...
```
The call site passes the let-binding; inside the wrapper, Z3 uses the equality to derive the expanded form.
