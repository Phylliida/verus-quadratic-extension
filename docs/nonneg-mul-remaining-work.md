# DTS nonneg_mul — Status & Remaining Work (2026-04-08, updated session 2)

## Current State: Error A FIXED, Error B WIP

Started at 122 verified, 2 errors. This session fixed Error A completely (reverse Cauchy). Error B has correct mathematical structure but helpers need same_radicand chain fixes (4 precondition errors).

**Fully verified (including new):**
- `lemma_reverse_cauchy_nonneg_re_from_pos_norms` — pos norms + neg(dd*b1*b2) → nonneg(re_val)
- `lemma_dts_nonneg_mul_iszero_im` (im=0 handler) — ALL cases
- `lemma_dts_nonneg_mul_closed_fuel` (main entry)
- All sub-helpers (cauchy steps, le chains, square_le, etc.)

**Still WIP (precondition fixes needed):**
- `lemma_neg_norms_nonneg_re_val` — both norms neg → nonneg(re_val)
- `lemma_mixed_norms_nonneg_im_val` — mixed norms → nonneg(im_val)
- `lemma_dts_nonneg_mul_remaining` — depends on above two
- `lemma_dts_nonneg_add_closed_fuel` — cascading from remaining

## Error A (FIXED)

**Location:** !nonneg(im), nx≥0&&ny≥0, neg(dd*b1*b2)≥0 path.

**Solution:** `lemma_reverse_cauchy_nonneg_re_from_pos_norms` at (f, 5nat).
- Calls `cauchy_le_transitive_raw` → sub(a1sq*a2sq, db2sq*db1sq) ≥ 0
- Congruence chain: a1sq*a2sq ≡ (a1*a2)², db2sq*db1sq ≡ neg(db1b2)²
- `square_le_implies_le(neg(db1b2), a1a2)` → sub(a1a2, neg(db1b2)) ≥ 0
- neg_involution + congruence → nonneg(add(a1a2, db1b2)) = nonneg(re_val)

## Error B (WIP)

**Location:** !nonneg(im), !nonneg(re), NOT (nx≥0 && ny≥0) — end of function body.

**Three sub-cases:**

### Sub-case 1: neg(nx)≥0 && neg(ny)≥0 (both norms negative)
**Helper:** `lemma_neg_norms_nonneg_re_val` at (f, 6nat)
**Status:** Mathematical structure complete. 4 sr chain precondition errors.
**Approach:**
1. `nonneg_im_from_neg_norm` → nonneg(b1), nonneg(b2)
2. Case split on a1*a2:
   - nonneg(a1*a2): nonneg_mul(b1,b2) + nonneg_mul(dd, b1*b2) + nonneg_add → nonneg(re_val)
   - neg(a1*a2): Direct le chain dd*b1²*dd*b2² ≥ a1²*a2² → `cauchy_neg_a1a2_square_le` → nonneg(re_val)
3. nonneg(re_val) + !nonneg(re_val) → contradiction → postcondition

**Remaining fix:** Same-radicand transitive calls before add_closed, sub_congruence_both, and norm_definite_add.

### Sub-cases 2+3: Mixed norms (one positive, one negative)
**Helper:** `lemma_mixed_norms_nonneg_im_val` at (f, 6nat)
**Status:** Mathematical structure complete. sr chain precondition errors.
**Key insight:** With mixed norms, the Cauchy argument derives nonneg(IM) not nonneg(RE).
- From positive-norm factor: nonneg(a1) via nonneg_re_from_nonneg_norm
- From negative-norm factor: nonneg(b2) via nonneg_im_from_neg_norm
- Le chain: a1²*b2² ≥ dd*b1²*b2² ≡ dd*b2²*b1² ≥ a2²*b1² → (a1*b2)²≥(b1*a2)²
- Case split: nonneg(b1*a2) → nonneg_add; neg(b1*a2) → square_le_implies_le
- Both give nonneg(add(a1*b2, b1*a2)) = nonneg(im_val)
- nonneg(im_val) + !nonneg(im_val) → contradiction → postcondition

**Symmetric case:** For neg(nx)≥0, ny≥0: call with swapped factors (a1↔a2, b1↔b2), then commutative congruence chain to convert add(a2*b1, b2*a1) ≡ add(a1*b2, b1*a2).

**Remaining fix:** Same pattern — add transitive calls for sr chains.

## Pattern for Fixing sr Chain Errors

Every `add_closed(x, neg(y))` needs:
```rust
lemma_dts_same_radicand_neg(y);  // sr(y, neg(y))
lemma_dts_same_radicand_transitive(x, y, dts_neg(y));  // sr(x, neg(y))
lemma_dts_add_closed(x, dts_neg(y));
```

Every `norm_definite_add(x, neg(y))` needs the same sr chain.

Every `sub_congruence_both(a, b, c, d)` needs sr(a, c) and sr(b, d).

## Decreases Hierarchy (Updated)

| Function | Decreases | Status |
|----------|-----------|--------|
| nonneg_mul_closed | (fuel, 0) | **verified** |
| nonneg_add_closed | (fuel, 0) | cascading error |
| cauchy_schwarz_step | (fuel, 1) | **verified** |
| le_antisymmetric | (fuel, 1) | **verified** |
| nonneg_fuel_congruence | (fuel, 2) | **verified** |
| cauchy_schwarz_combine | (fuel, 2) | **verified** |
| nonneg_re_from_neg_im | (fuel, 2) | **verified** |
| nonneg_im_from_neg_norm | (fuel, 2) | **verified** |
| nonneg_re_from_nonneg_norm | (fuel, 2) | **verified** |
| nonneg_component_from_ext | (fuel, 3) | **verified** |
| iszero_re_from_neg_norm_product | (fuel, 3) | **verified** |
| le_chain_neg_norms | (fuel, 3) | **verified** |
| square_le_implies_le | (fuel, 3) | **verified** |
| cauchy_le_transitive_raw | (fuel, 3) | **verified** |
| neg_a1a2_square_le | (fuel, 4) | **verified** |
| cauchy_neg_db1b2_case | (fuel, 4) | **verified** |
| **reverse_cauchy_nonneg_re** | (fuel, 5) | **verified** (new) |
| cauchy_schwarz_is_zero_re | (fuel, 5) | **verified** |
| cauchy_neg_a1a2_from_na2sq | (fuel, 5) | **verified** |
| cauchy_nonneg_re_dispatch | (fuel, 6) | **verified** |
| nonneg_mul_iszero_im | (fuel, 6) | **verified** |
| **neg_norms_nonneg_re_val** | (fuel, 6) | **WIP** (new) |
| **mixed_norms_nonneg_im_val** | (fuel, 6) | **WIP** (new) |
| nonneg_mul_remaining | (fuel, 7) | **1 error** (down from 2) |

## File: `verus-quadratic-extension/src/dyn_tower_lemmas.rs`
- **reverse_cauchy_nonneg_re:** ~line 3542 (VERIFIED)
- **neg_norms_nonneg_re_val:** ~line 3797 (WIP)
- **mixed_norms_nonneg_im_val:** ~line 4138 (WIP)
- **Error B call site:** ~line 13720
