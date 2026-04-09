# DTS nonneg_mul — Status & Remaining Work (2026-04-09, session 4)

## Current State: 127 verified, 1 real error + 1 cascading

Started session 4 at 126 verified, 2 errors. Created `lemma_nonneg_mul_neg_im_path` helper (+1 verified). Found and partially fixed a previously-masked fall-through in the nonneg(im) handler.

## What Was Done This Session

### !nonneg(im) Path: FIXED (via clean-context helper)

**Problem:** Z3 context pollution in the 800-line `nonneg_mul_remaining` function. The `!nonneg(im_val)` fact was lost after 630 lines of the nonneg(im) handler. Even simple boolean variables were lost over this distance. rlimit increases (up to 10000) didn't help — the issue is context pollution, not time.

**Solution:** Created `lemma_nonneg_mul_neg_im_path` (~370 lines, rlimit 500, decreases (f, 8nat)). This handles the entire `!nonneg(im)` path in a clean context:
- Pos norms (nx≥0, ny≥0): derive nonneg(re_val) via nonneg_re_from_nonneg_norm + nonneg_add/reverse_cauchy → conclude_re. Also establish nonneg(norm_product) via nonneg_mul_closed(nx2, ny2) + norm_mul congruence chain for the conclude_re precondition.
- Neg norms (neg(nx)≥0, neg(ny)≥0): derive nonneg(re_val) via neg_norms_nonneg_re_val. Establish nonneg(norm_product) via neg_mul_neg(nx2, ny2) congruence. → conclude_re.
- Mixed norms: call mixed_norms_nonneg_im_val → nonneg(im_val) → contradicts `!im_nonneg` from requires → false → postcondition. The swap case (neg(nx)≥0, ny≥0) includes the full 70-line congruence chain (mul_commutative + add_congruence + eqv_transitive).

**Key techniques that worked:**
- **Direct negation requires** instead of ghost boolean params. The helper's requires includes `!dts_nonneg_fuel(dts_add(dts_mul(a1, b2), dts_mul(b1, a2)), f)` directly.
- **Early if-check exit** before the nonneg(im) handler with `if/else` structure to avoid dead code.
- `nonneg_mul_remaining` bumped from `decreases f, 8nat` to `(f, 9nat)`.

**What was tried but didn't work:**
- Ghost boolean params (`im_nonneg: bool` with `im_nonneg == ...`): Z3 still loses the boolean over 630 lines.
- Two separate if-checks (`if !im { return; } if im { ... }`): Z3 can't connect them to eliminate dead code.
- `ensures false` on error_b_dispatch with `!re_nonneg, !im_nonneg`: can't call from nonneg(re) paths.
- Increasing rlimit (tested up to 10000): doesn't help context pollution.

### error_b_dispatch: Modified to derive nonneg_or_neg internally (Option 2)

Removed the two `nonneg_or_neg` disjunction preconditions from `error_b_dispatch`. Added ~50 lines of norm infrastructure at the top of its body to derive `nonneg_or_neg(nx, f)` and `nonneg_or_neg(ny, f)` internally. This required wf/depth/sr chains for both nx and ny.

### Newly Uncovered Error: Fall-through in nonneg(im) handler

With the `!nonneg(im)` path fixed by the helper, Z3 now reports a postcondition error in the nonneg(im) handler itself. This was previously MASKED by the error_b_dispatch failure.

**Root cause:** Two missing `return` paths in the nonneg(im) handler:

1. **nonneg(a1*a2) + nonneg(b1*neg_b2) path** (inside `if nonneg(b1*neg_b2)` block at ~line 14448): The `if !nonneg(a1*a2) { ... all return ... }` block handles the `!nonneg(a1*a2)` case. When `nonneg(a1*a2)` IS true, the code falls through with no return. **Partially fixed** with explicit Cauchy proof: pos norms → reverse_cauchy, neg norms → nonneg_im_from_neg_norm + nonneg_add → nonneg(re_val) → conclude_re.

2. **!nonneg(b1*neg_b2) path** (after the `if nonneg(b1*neg_b2) { ... }` block): No code handles this case at all. **This is the remaining error.**

## Remaining: !nonneg(b1*neg_b2) Path

### The Problem

After the `if dts_nonneg_fuel(dts_mul(b1, neg_b2), f) { ... }` block at ~line 14448, the code falls through when `!nonneg(b1*neg_b2)`. There's no `else` clause. The code at this point needs to establish `nonneg(Ext(re_val, im_val, dd), f+1)`.

### Context

At this point:
- nonneg(im_val) from the nonneg(im) handler's else clause
- `!nonneg(b1*neg_b2)` from the if-check
- We're inside the else at ~line 14095 which handles "both same-sign norms" (NOT mixed norms — those returned earlier at lines 14060/14078)
- `neg_b2 = dts_neg(b2)` defined at line 14120 — **530 lines away from the current code**

### Why It's Hard

The `neg_b2` let-binding at line 14120 is 530 lines from the code that needs it. Z3 loses `neg_b2 == dts_neg(b2)`. This means:
- Can't establish `sr(b1, neg_b2)` (needs `sr(b2, neg_b2)` which needs the let-binding)
- Can't establish `wf(neg_b2)`, `depth(neg_b2)`, `nonneg_radicands(neg_b2)`, `norm_definite(neg_b2)` (all derive from `dts_neg(b2)` but Z3 can't connect to `neg_b2`)
- Can't call `nonneg_mul_closed(b1, neg_b2)` to derive the contradiction `nonneg(b1*neg_b2)` for the unreachable mixed-b-signs case

### Mathematical Analysis

With same-sign norms (both pos or both neg) and `!nonneg(b1*neg_b2)`:
- b1*neg_b2 < 0 means b1 and neg_b2 have different signs → b1 and b2 have the SAME sign
- **Pos norms:** a1² ≥ dd*b1², a2² ≥ dd*b2². Cauchy: (a1*a2)² ≥ (dd*b1*b2)². Since b1*b2 ≥ 0 (same sign): dd*b1*b2 ≥ 0. With nonneg(a1*a2) from nonneg_re_from_nonneg_norm: re_val = a1*a2 + dd*b1*b2 ≥ 0 via nonneg_add. **But** establishing nonneg(b1*b2) needs case-split on b-signs, and mixed-b-signs contradiction needs `neg_b2` infrastructure.
- **Neg norms:** dd*b1² ≥ a1², dd*b2² ≥ a2². With norm_definite: nonneg(b1), nonneg(b2). dd ≥ 0. So dd*b1*b2 ≥ 0. nonneg(a1*a2) from neg_a*neg_a or direct. re_val = a1*a2 + dd*b1*b2 ≥ 0 via nonneg_add.

In ALL cases with same-sign norms: nonneg(re_val) holds. So nonneg(re_val) + nonneg(im_val) → C1 → nonneg(Ext). The path where `!nonneg(re_val)` is **mathematically unreachable** from this context.

### Proposed Fix: Clean-Context Helper

Create a helper `lemma_nonneg_mul_same_sign_norms` at decreases (f, 8nat) that derives `nonneg(Ext(re_val, im_val, dd))` when both norms have the same sign (not mixed).

**Signature:**
```rust
proof fn lemma_nonneg_mul_same_sign_norms<T: OrderedField>(
    a1, b1, a2, b2, dd: DynTowerSpec<T>, f: nat,
)
    requires
        // Standard infrastructure (same as nonneg_mul_remaining)
        ...
        // Both factors nonneg at fuel f+1
        ...
        // NOT mixed norms (both same sign)
        // One of: (nonneg(nx) && nonneg(ny)) || (nonneg(neg(nx)) && nonneg(neg(ny)))
        // Can derive this internally via nonneg_or_neg + the NOT-mixed-norms constraint
        // Actually: just require NOT mixed norms:
        !(dts_nonneg_fuel(dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1))), f)
          && dts_nonneg_fuel(dts_neg(dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2)))), f)),
        !(dts_nonneg_fuel(dts_neg(dts_sub(dts_mul(a1, a1), dts_mul(dd, dts_mul(b1, b1)))), f)
          && dts_nonneg_fuel(dts_sub(dts_mul(a2, a2), dts_mul(dd, dts_mul(b2, b2))), f)),
        // nonneg(im_val)
        dts_nonneg_fuel(dts_add(dts_mul(a1, b2), dts_mul(b1, a2)), f),
        !dts_is_zero(dts_add(dts_mul(a1, b2), dts_mul(b1, a2))),
    ensures
        dts_nonneg_fuel(Ext(re_val, im_val, dd), (f+1)),
```

**Body approach:**
1. Re-derive product infrastructure (~30 lines)
2. Re-derive norm infrastructure for nx, ny (~50 lines)
3. norm_mul identity
4. nonneg_or_neg on nx, ny → same-sign dispatch:
   - Pos norms: nonneg_re_from_nonneg_norm → nonneg(a1), nonneg(a2). nonneg(b1*b2) via both-nonneg or neg_mul_neg. nonneg_add → nonneg(re_val). nonneg_mul(nx, ny) → nonneg(norm_product). conclude_re.
   - Neg norms: neg_norms_nonneg_re_val → nonneg(re_val). neg_mul_neg(nx, ny) → nonneg(norm_product). conclude_re.

**Alternative simpler approach:** Don't create a new helper. Instead, modify the existing `neg_im_path` helper to NOT require `!nonneg(im)`. The pos norms and neg norms cases already establish nonneg(re_val) + nonneg(norm_product) → conclude_re (which works regardless of im sign). Only the mixed norms case uses the !nonneg(im) contradiction. For the nonneg(im) case in the caller, mixed norms don't apply (already returned at lines 14060/14078). So the mixed norms branch is unreachable — but Z3 needs to verify it anyway. With nonneg(im), mixed_norms gives nonneg(im) which is already true but doesn't help establish nonneg(Ext). Need nonneg(re) or nonneg(norm) too. So the mixed norms case would need additional handling.

**Simplest approach:** At the call site, just call the existing verified helpers directly:
```rust
// !nonneg(b1*neg_b2) path: same-sign norms → nonneg(re_val).
// Call the neg_im_path helper but only for pos/neg norms:
lemma_dts_nonneg_or_neg_nonneg_fuel(re_val_local, f_local);
if nonneg(re_val) {
    conclude_re;
    return;
}
// !nonneg(re): call neg_norms or pos_norms helper → nonneg(re) → contradiction
```

But this needs re_val infrastructure (wf, depth) which Z3 loses.

**Bottom line:** The fix requires a clean-context helper for the same-sign norms case. The helper is ~120-150 lines (norm infrastructure + pos/neg dispatch + conclude_re). Place it right before `nonneg_mul_remaining`.

## Decreases Hierarchy (Final)

| Function | Decreases | Status |
|----------|-----------|--------|
| nonneg_mul_closed | (fuel, 0) | **verified** |
| nonneg_add_closed | (fuel, 0) | cascading error |
| cauchy_schwarz_step | (fuel, 1) | **verified** |
| le_antisymmetric | (fuel, 1) | **verified** |
| nonneg_fuel_congruence | (fuel, 2) | **verified** |
| nonneg_or_neg | (fuel, 2) | **verified** |
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
| reverse_cauchy_nonneg_re | (fuel, 5) | **verified** |
| cauchy_schwarz_is_zero_re | (fuel, 5) | **verified** |
| cauchy_neg_a1a2_from_na2sq | (fuel, 5) | **verified** |
| cauchy_nonneg_re_dispatch | (fuel, 6) | **verified** |
| nonneg_mul_iszero_im | (fuel, 6) | **verified** |
| neg_norms_nonneg_re_val | (fuel, 6) | **verified** |
| mixed_norms_nonneg_im_val | (fuel, 6) | **verified** |
| error_b_dispatch | (fuel, 7) | **verified** |
| **nonneg_mul_neg_im_path** | **(fuel, 8)** | **verified** (new) |
| nonneg_mul_remaining | (fuel, 9) | **1 error** (bumped from 8) |

## File Locations

All changes in `verus-quadratic-extension/src/dyn_tower_lemmas.rs`:

| Function | ~Line | Status |
|----------|-------|--------|
| error_b_dispatch (modified) | ~13251 | VERIFIED (internal nonneg_or_neg) |
| **nonneg_mul_neg_im_path** | **~13437** | **VERIFIED** (new, ~370 lines) |
| nonneg_mul_remaining | ~13808 | 1 error (fall-through in nonneg(im) handler) |
| Fall-through: nonneg(a1*a2) + b1*neg_b2 | ~14490 | Partially fixed (Cauchy dispatch) |
| Fall-through: !nonneg(b1*neg_b2) | ~14616 | **REMAINING ERROR** |

## Key Z3 Context Pollution Lessons

1. **Z3 loses even boolean variables** over 630 lines. Don't rely on control flow facts propagating more than ~200 lines.
2. **Let-binding connections** (e.g., `neg_b2 == dts_neg(b2)`) are lost over 530 lines. ALL derived facts that depend on the let-binding become unusable.
3. **rlimit increases don't help** context pollution (tested up to 10000). The issue is Z3 losing facts, not running out of time.
4. **Clean-context helpers are the ONLY reliable fix** for functions >200 lines. Ghost equality params + short variable chains work well inside helpers.
5. **`return` per branch** prevents cross-branch context pollution and helps Z3 check postconditions locally.
6. **`if/else` structure** is needed to avoid dead code paths (two separate if-checks leave dead code that Z3 can't close).
7. **Use let-variables** (not expanded forms) in calls that need to match earlier if-checks — but only if the let-binding is within ~100 lines.
