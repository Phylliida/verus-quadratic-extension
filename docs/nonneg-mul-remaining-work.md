# DTS nonneg_mul — Status & Remaining Work (2026-04-08, updated)

## Current State: 122 verified, 2 errors

Started at 96 verified (multi-session effort). Reached 117/3 errors, then this session fixed iszero_im completely and most of nonneg_mul_remaining.

**Fully verified:**
- `lemma_dts_nonneg_mul_iszero_im` (im=0 handler) — ALL cases
- `lemma_dts_nonneg_mul_closed_fuel` (main entry)
- All sub-helpers (cauchy_schwarz_step/combine, le_chains, square_le, etc.)

**Still failing:**
- `lemma_dts_nonneg_mul_remaining` (im≠0 handler) — 2 error exit points
- `lemma_dts_nonneg_add_closed_fuel` — cascading from remaining

## What Was Done

### New Helpers Created (all verified)

| Helper | Decreases | What it does |
|--------|-----------|-------------|
| `nonneg_im_from_neg_norm` | (f, 2nat) | neg(norm)≥0 + Ext nonneg + norm_definite → nonneg(b). C2 impossible: norm_definite + is_zero(norm) → is_zero(b) contradicts !is_zero(b). |
| `nonneg_re_from_nonneg_norm` | (f, 2nat) | nonneg(norm) + Ext nonneg + norm_definite → nonneg(a). C3 impossible: norm_definite + is_zero(norm) → is_zero(a) contradicts !is_zero(a). |
| `iszero_re_from_neg_norm_product` | (f, 3nat) | nonneg(neg(nx*ny)) + is_zero(im) → nonneg(re_val). Via norm_mul eqv + sub_zero chain (im=0 → re² ≡ nx*ny) → le_antisymmetric → is_zero(re²) → mul_cancel_zero → nonneg. |
| `cauchy_neg_a1a2_from_na2sq` | (f, 5nat) | Congruence bridge: converts Q²≥P² from `na2_sq*a1_sq` form to `a1_sq*a2_sq` form via neg_mul_neg + mul_commutative, then calls `cauchy_neg_a1a2_square_le`. |

### Key Fixes Applied

1. **iszero_im neg(nx)&&neg(ny)**: Used nonneg_im_from_neg_norm to derive b1≥0, b2≥0 (C2 impossible when neg(norm)≥0 + norm_definite). Then case split on a1*a2: nonneg → nonneg_add; neg → cauchy_neg_a1a2_from_na2sq.

2. **iszero_im mixed-sign norms** (neg(nx)&&ny, nx&&neg(ny)): Used iszero_re_from_neg_norm_product to derive nonneg(re_val) from nonneg(neg(nx*ny)) via the norm_mul + is_zero(im) simplification chain.

3. **iszero_im dead code**: Removed ~270 lines of old is_zero proof path, replaced by the above two clean-context helpers.

4. **remaining !b1&&!b2 path**: Local if-checks for nonneg_re_from_neg_im (Z3 sees !nonneg(b) immediately → derives nonneg(neg(b))).

5. **remaining nonneg(im) + !nonneg(a1*a2) + b1≥0||b2≥0**: For nx≥0&&ny≥0: nonneg_re_from_nonneg_norm → nonneg(a1), nonneg(a2) → nonneg(a1*a2) → contradiction. For neg norms: nonneg_im_from_neg_norm + Cauchy bridge → nonneg(re_val) → contradiction.

6. **remaining !nonneg(im) + nonneg(re)**: conclude_re handles this directly.

7. **remaining !nonneg(im) + nx≥0&&ny≥0 + nonneg(dd*b1*b2)**: nonneg_re_from_nonneg_norm → nonneg(a1*a2), then nonneg_add → nonneg(re_val) → contradiction.

8. **remaining dead code**: Removed ~400 lines of old P*S congruence chain that was always failing due to Z3 context pollution.

## Remaining 2 Errors

Both are in `lemma_dts_nonneg_mul_remaining`, at two `return;` exit points.

### Error A: nx≥0&&ny≥0, !nonneg(re), !nonneg(im), neg(dd*b1*b2)≥0

**Location:** `!nonneg(im)` handler, inside `if nx2>=0 && ny2>=0`, after the `if nonneg(dd*b1*b2)` block (the else/fallthrough).

**What's established:**
- nonneg(a1) and nonneg(a2) via `nonneg_re_from_nonneg_norm`
- nonneg(a1*a2) via `nonneg_mul_closed`
- neg(dd*b1*b2)≥0 (from the else of nonneg_or_neg)

**What's needed:** nonneg(re_val) where re_val = a1*a2 + dd*b1*b2.

**Mathematical argument (reverse Cauchy):**
- From norms: a1²≥dd*b1² (nx≥0) and a2²≥dd*b2² (ny≥0)
- le_mul_nonneg_monotone chain: a1²*a2² ≥ dd*b1²*a2² ≥ dd*b1²*dd*b2² = (dd*b1*b2)²
- So (a1*a2)² ≥ (dd*b1*b2)² via square_mul congruences
- With nonneg(a1*a2) and nonneg(neg(dd*b1*b2)):
  - square_le_implies_le(neg(dd*b1*b2), a1*a2) → a1*a2 ≥ neg(dd*b1*b2)
  - sub(a1*a2, neg(dd*b1*b2)) = add(a1*a2, dd*b1*b2) = re_val ≥ 0

**Implementation approach:**
Create a clean-context helper `lemma_dts_nonneg_re_from_pos_norms` that:
1. Takes nonneg(nx), nonneg(ny), Ext nonneg for both factors, standard infrastructure
2. Derives nonneg(a1), nonneg(a2) via `nonneg_re_from_nonneg_norm`
3. Sets up the le_mul_nonneg_monotone chain (dual of the Cauchy step — norms in opposite direction)
4. Calls square_le_implies_le or handles both dd*b1*b2 signs directly
5. Ensures nonneg(re_val)

**Estimated complexity:** ~120 lines (similar to cauchy_neg_a1a2_square_le but with reversed norm direction). The le_mul chain and square_mul congruences are the same pattern, just with a1²≥dd*b1² instead of dd*b1²≥a1².

### Error B: Mixed/neg norms + !nonneg(re) + !nonneg(im) (function body end)

**Location:** End of `lemma_dts_nonneg_mul_remaining`, after the `!nonneg(im)` handler.

**What this is:** The path where `!nonneg(im)` AND either mixed norms or neg norms AND !nonneg(re) after the nx≥0&&ny≥0 handler.

**Sub-cases:**

1. **neg(nx)≥0 && neg(ny)≥0 + !nonneg(re) + !nonneg(im):** Same Cauchy argument as iszero_im's neg norms case. nonneg_im_from_neg_norm → b1≥0, b2≥0. Case split on a1*a2: nonneg → nonneg_add; neg → cauchy bridge. All derive nonneg(re_val) → contradicts !nonneg(re_val). **Needs norm_definite(Ext(a2,b2,dd))** as a precondition (same as iszero_im fix).

2. **Mixed norms (neg(nx)≥0&&ny≥0 or nx≥0&&neg(ny)≥0) + !nonneg(re) + !nonneg(im):** This path is unreachable. Proof sketch:
   - Mixed norms → nonneg(neg(nx*ny)) via neg_mul chain → product norm ≤ 0
   - For the product to be nonneg: C1 needs nonneg(re)&&nonneg(im) — both fail. C3 needs nonneg(im) — fails. C2 needs nonneg(re)&&nonneg(norm) — norm≤0 from mixed, so need is_zero(norm).
   - is_zero(norm) → mul_cancel_zero → one factor norm is zero → norm_definite → one factor is zero → product is zero → nonneg trivially.
   - But we need to actually DERIVE nonneg(re_val), not assume the product is nonneg. The key is: for C2 to work, norm must be 0. With is_zero(norm) → one factor zero → re_val = 0 → nonneg(0). So this path either gives nonneg(re_val) = nonneg(0), or is genuinely unreachable.

**Implementation approach for sub-case 1:** Reuse the same code pattern as in the nonneg(im) path's neg-norms handler. Call nonneg_im_from_neg_norm for both factors, then Cauchy bridge. Need to add norm_definite(Ext(a2,b2,dd)) to nonneg_mul_remaining's preconditions (and verify the caller provides it).

**Implementation approach for sub-case 2:** Derive nonneg(neg(nx*ny)) from mixed norms (already done in nonneg(im) path's lines 12376-12410). Then show is_zero(norm) → one factor zero → product zero → nonneg. OR: just call iszero_re_from_neg_norm_product if is_zero(im) — but im≠0 here! Need a new helper for the "mixed norms → one norm is zero → factor is zero" argument.

**Estimated complexity:** Sub-case 1: ~30 lines (reuse existing helpers, need norm_definite precondition). Sub-case 2: ~60-80 lines for the is_zero(norm) → factor zero argument.

## Techniques Reference

### What works in large functions (>200 lines)

| Technique | When to use |
|-----------|-------------|
| Clean-context helper | Congruence chains, le_mul chains, any 20+ line proof block |
| Local if-recheck | When a fact from an earlier guard is needed: `if !nonneg(x) { use_neg(x); }` |
| Ghost equality params | Let-binding match at call sites: `wrapper(..., nx) requires nx == sub(...)` |
| Early fact establishment | Prove consequences at the if-check point, not 300 lines later |
| `return` per branch | Isolates postcondition checking, prevents cross-branch pollution |

### What doesn't work

| Anti-pattern | Why it fails |
|-------------|-------------|
| Simple `assert(fact)` hints | Z3 context too large, assertion verification itself may fail |
| `nonneg_or_neg` without local if-check | Gives disjunction but Z3 can't connect to the if-guard |
| Inline congruence chains in 700-line functions | Z3 loses sr/wf facts after ~50 intervening assertions |
| Structural equality for neg(zero) | Must use eqv via `lemma_neg_zero::<T>()` |

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
| **nonneg_im_from_neg_norm** | (fuel, 2) | **verified** (new) |
| **nonneg_re_from_nonneg_norm** | (fuel, 2) | **verified** (new) |
| nonneg_component_from_ext | (fuel, 3) | **verified** |
| **iszero_re_from_neg_norm_product** | (fuel, 3) | **verified** (new) |
| le_chain_neg_norms | (fuel, 3) | **verified** |
| square_le_implies_le | (fuel, 3) | **verified** |
| neg_a1a2_square_le | (fuel, 4) | **verified** |
| cauchy_schwarz_is_zero_re | (fuel, 5) | **verified** |
| **cauchy_neg_a1a2_from_na2sq** | (fuel, 5) | **verified** (new) |
| cauchy_nonneg_re_dispatch | (fuel, 6) | **verified** |
| nonneg_mul_iszero_im | (fuel, 6) | **verified** |
| nonneg_mul_remaining | (fuel, 7) | **2 errors** |

## File: `verus-quadratic-extension/src/dyn_tower_lemmas.rs`

All changes are in this one file (~13000 lines). Key locations for the remaining work:

- **Error A site:** Search for `neg(dd*b1*b2) case: TODO` (~line 12990)
- **Error B site:** Search for `Mixed or neg norms + !nonneg(re) + !nonneg(im)` (~line 13000)
- **nonneg_im_from_neg_norm:** ~line 1860
- **nonneg_re_from_nonneg_norm:** ~line 1860
- **cauchy_neg_a1a2_from_na2sq:** ~line 1927
- **iszero_re_from_neg_norm_product:** ~line 1927
- **cauchy_neg_a1a2_square_le:** ~line 2700
- **nonneg_mul_iszero_im:** ~line 11517
- **nonneg_mul_remaining:** ~line 12193
