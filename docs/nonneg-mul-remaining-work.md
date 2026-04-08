# DTS nonneg_mul — Status & Remaining Work (2026-04-08, session 3)

## Current State: 126 verified, 1 real error + 1 cascading

Started this session at 122 verified, 2 errors. Fixed Error A completely. All Error B helpers verified. Final integration at the call site remains.

## What Was Done This Session

### Error A: FIXED
Created `lemma_reverse_cauchy_nonneg_re_from_pos_norms` at (f, 5nat).

**Problem:** In the `!nonneg(im)` path with positive norms (nx>=0, ny>=0), when neg(dd*b1*b2)>=0, needed to derive nonneg(re_val = a1*a2 + dd*b1*b2).

**Solution:** Reverse Cauchy argument. From positive norms: (a1*a2)^2 >= (dd*b1*b2)^2. With nonneg(a1*a2) and nonneg(neg(dd*b1*b2)): square_le_implies_le -> a1*a2 >= neg(dd*b1*b2) -> re_val >= 0.

**Implementation:** ~250 lines. Calls `cauchy_le_transitive_raw` for the le_mul chain, then congruence chain (dd_sq_product_eqv + square_mul) to squared form, then square_le_implies_le, then neg_involution conversion.

### Error B: All Helpers Verified, Call Site Integration Remaining

Created 3 new helpers + 1 dispatch function:

| Helper | Decreases | Lines | Status |
|--------|-----------|-------|--------|
| `lemma_neg_norms_nonneg_re_val` | (f, 6nat) | ~310 | VERIFIED |
| `lemma_mixed_norms_nonneg_im_val` | (f, 6nat) | ~420 | VERIFIED |
| `lemma_error_b_dispatch` | (f, 7nat) | ~100 | VERIFIED |

#### `lemma_neg_norms_nonneg_re_val`
Both norms negative -> nonneg(re_val). From neg(norm)>=0 + norm_definite: nonneg(b1), nonneg(b2). Case split on a1*a2:
- nonneg(a1*a2): nonneg_mul(b1,b2) + nonneg_mul(dd, b1*b2) + nonneg_add -> nonneg(re_val)
- neg(a1*a2): Direct le chain (dd*b1^2*dd*b2^2 >= a1^2*a2^2) + cauchy_neg_a1a2_square_le -> nonneg(re_val)

#### `lemma_mixed_norms_nonneg_im_val`
**Key insight:** With mixed norms, the Cauchy argument works for the IM component, not the RE component.

From positive-norm factor: nonneg(a1) via nonneg_re_from_nonneg_norm. From negative-norm factor: nonneg(b2) via nonneg_im_from_neg_norm. Le chain: a1^2*b2^2 >= dd*b1^2*b2^2 = dd*b2^2*b1^2 >= a2^2*b1^2. So (a1*b2)^2 >= (b1*a2)^2. Then:
- nonneg(b1*a2): nonneg_add -> nonneg(im_val)
- neg(b1*a2): square_le_implies_le -> nonneg(im_val)

Has `#[verifier::rlimit(40)]` due to function size.

#### `lemma_error_b_dispatch`
Case splits on norm signs and calls the appropriate helper:
- neg(nx)&&neg(ny): calls neg_norms_nonneg_re_val
- nx>=0: calls mixed_norms_nonneg_im_val (standard direction)
- else (neg(nx), ny>=0): calls mixed_norms_nonneg_im_val with swapped factors + congruence chain to convert add(a2*b1, b2*a1) to add(a1*b2, b1*a2) = im_val

Ensures: `nonneg(re_val) || nonneg(im_val)` (caller derives contradiction with !nonneg from control flow).

## Remaining: Call Site Integration

### The Problem

`lemma_dts_nonneg_mul_remaining` (~800 lines) calls `lemma_error_b_dispatch` at the Error B site. The dispatch helper has many preconditions. Z3 in the 800-line function context cannot satisfy them due to context pollution. Even rlimit(1000) doesn't help — the issue is fundamental Z3 context loss, not time.

### What Specifically Fails

The call at ~line 14188:
```rust
lemma_dts_nonneg_or_neg_nonneg_fuel(nx2, f);
lemma_dts_nonneg_or_neg_nonneg_fuel(ny2, f);
lemma_error_b_dispatch(a1, b1, a2, b2, dd, f, nx2, ny2);
```

The dispatch requires:
1. **nonneg_or_neg disjunctions** for nx2, ny2 — the `nonneg_or_neg` calls at the call site need well_formed and depth for nx2/ny2, which were established ~500 lines earlier but Z3 lost them
2. **NOT(nx2>=0 && ny2>=0)** — from the earlier if-check + return, but Z3 may not track this
3. **Standard infrastructure** (well_formed, same_radicand, etc.) — from function requires, should propagate but Z3 is overwhelmed
4. **norm_definite(Ext(a1,b1,dd))** — from requires, but 800 lines away

### Proposed Solutions (in order of likely effectiveness)

#### Option 1: Extract !nonneg(im) path into helper (RECOMMENDED)

The entire code path after `if nonneg(im) { ... }` is the !nonneg(im) handler (~100 lines including Error A + Error B). Extract it into `lemma_nonneg_mul_remaining_neg_im` at (f, 8nat) with explicit preconditions including:
- `!nonneg(im_val)` and `!nonneg(re_val)`
- All norm infrastructure (well_formed, depth for nx2/ny2)
- nonneg_or_neg results as preconditions

This eliminates the 700 lines of nonneg(im) handler from Z3's context. The new helper would be ~150 lines (manageable for Z3).

From `nonneg_mul_remaining`, call both: `if nonneg(im) { ... nonneg_im_handler ... } else { neg_im_handler(...); }` — no fall-through.

#### Option 2: Simplify dispatch preconditions

Remove the nonneg_or_neg disjunction preconditions from `error_b_dispatch` and derive them internally (call nonneg_or_neg inside the dispatch with the needed infrastructure). This requires adding ~30 lines of depth/wf establishment to the dispatch function, but it's a clean context so it should work.

#### Option 3: Ghost equality params for nonneg_or_neg results

Instead of requiring the disjunction as a precondition, pass 4 ghost boolean params indicating which branch of nonneg_or_neg holds:
```rust
nx_nonneg: bool, ny_nonneg: bool,
requires
    nx_nonneg == dts_nonneg_fuel(nx, f),
    !nx_nonneg ==> dts_nonneg_fuel(dts_neg(nx), f),
    ...
```

This makes Z3's job trivial at the call site (just pass the booleans from if-checks).

## Decreases Hierarchy (Final)

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
| **neg_norms_nonneg_re_val** | (fuel, 6) | **verified** (new) |
| **mixed_norms_nonneg_im_val** | (fuel, 6) | **verified** (new) |
| **error_b_dispatch** | (fuel, 7) | **verified** (new) |
| nonneg_mul_remaining | (fuel, 8) | **1 error** (bumped from 7) |

## File Locations

All changes in `verus-quadratic-extension/src/dyn_tower_lemmas.rs`:

| Function | ~Line | Status |
|----------|-------|--------|
| reverse_cauchy_nonneg_re | ~3542 | VERIFIED |
| neg_norms_nonneg_re_val | ~3797 | VERIFIED |
| mixed_norms_nonneg_im_val | ~4158 | VERIFIED |
| error_b_dispatch | ~13249 | VERIFIED |
| nonneg_mul_remaining | ~13398 | 1 error (call site) |
| Error B call site | ~14184 | precondition failure |

## Techniques Used (for future reference)

### What worked
- **Clean-context helpers** for all Cauchy arguments — Z3 can't handle congruence chains in 700+ line functions
- **Ghost equality params** (nx, ny) in error_b_dispatch — lets Z3 match let-bindings at call sites
- **`ensures false`** pattern for contradiction proofs — helper derives nonneg(X), caller has !nonneg(X)
- Changed to **`ensures nonneg(re) || nonneg(im)`** when `ensures false` required negative preconditions Z3 couldn't provide
- **return per branch** for postcondition isolation
- **neg_sub_swap** for converting neg(norm) to sub form for le_mul

### What didn't work
- Inline Error B code in 800-line function — Z3 context pollution
- Increasing rlimit (up to 1000) — problem is context loss, not time
- Re-establishing nonneg_or_neg inline — Z3 still can't connect to earlier if-checks
- `ensures false` with `!nonneg(X)` preconditions — caller Z3 can't provide negative facts from 700-line-ago if-checks

### Key same_radicand pattern
Every `add_closed(x, neg(y))` needs:
```rust
same_radicand_neg(y);                    // sr(y, neg(y))
same_radicand_transitive(x, y, neg(y));  // sr(x, neg(y))
add_closed(x, neg(y));                   // now passes
```

Same pattern for `norm_definite_add(x, neg(y))` and `sub_congruence_both`.
