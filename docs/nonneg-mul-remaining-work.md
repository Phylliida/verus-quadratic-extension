# DTS nonneg_mul — Remaining Work (2026-04-08)

## Current State: 117 verified, 3 errors

Started at 96 verified. All new helpers verified. The 3 remaining errors are in two functions (`nonneg_mul_remaining` and `nonneg_mul_iszero_im`) plus one cascading error in `nonneg_add_closed_fuel`.

## The One Mathematical Step That Fixes Everything

All 3 errors need the same mathematical argument: **the square_le bridge**.

Given: `nonneg(sub((dd*b1*b2)^2, (a1*a2)^2))` (Q^2 >= P^2 from Cauchy-Schwarz)
Derive: `nonneg(add(a1*a2, dd*b1*b2))` (re_val >= 0)

The proof:
1. Q^2 >= P^2 where Q = dd*b1*b2, P = a1*a2
2. square_le_implies_le(|P|, Q) -> Q >= |P| (needs nonneg(Q), nonneg(|P|))
3. sub(Q, |P|) >= 0
4. If P >= 0: sub(Q, P) >= 0 -> add(P, Q) >= 0 via algebra. Done.
5. If neg(P) >= 0: sub(Q, neg(P)) = add(Q, P) = add(P, Q) >= 0 via neg_involution. Done.

We already have `cauchy_neg_a1a2_square_le` (verified at f,4nat) that does steps 2-5 for the neg(P) case. And the nonneg(P) case is just nonneg_add.

The blocker: connecting Q^2 >= P^2 from `cauchy_schwarz_step + cauchy_schwarz_combine` (which uses `na2_sq = neg(a2)^2` and `a1_sq`) to the form needed by `cauchy_neg_a1a2_square_le` (which uses `db1_sq*db2_sq` and `a1_sq*a2_sq`). The congruence chain `dd_sq_product_eqv` bridges `db1_sq*db2_sq <-> (dd*b1*b2)^2`, and `square_mul` bridges `a1_sq*a2_sq <-> (a1*a2)^2`.

## Error 1: iszero_im neg(nx)&&neg(ny) !nonneg(re)

**File:** `dyn_tower_lemmas.rs`, function `lemma_dts_nonneg_mul_iszero_im`
**Location:** Inside `if neg(nx) && neg(ny)` block, after `if nonneg(re_val) { conclude_re; return; }`, at the `return;` with TODO comment.
**Decreases:** Currently (f, 6nat). Can bump higher if needed.

**What's established:** `nonneg(sub(dd_b1_sq*dd_b2_sq, na2_sq*a1_sq))` from `cauchy_schwarz_step + cauchy_schwarz_combine`.

**What's needed:** `nonneg(re_val)` where `re_val = add(a1*a2, dd*b1*b2)`.

**Approach:** 
1. Call `dd_sq_product_eqv(b1, b2, dd)` -> eqv(db1_sq*db2_sq, (dd*b1*b2)^2)
2. Congruence: na2_sq*a1_sq = neg(a2)^2 * a1^2 -> (a1*a2)^2 via neg_mul_neg + square_mul + mul_commutative
3. sub_congruence_both -> nonneg(sub((dd*b1*b2)^2, (a1*a2)^2))
4. This is the precondition of `cauchy_neg_a1a2_square_le` (if neg(a1*a2) >= 0) or a trivial nonneg_add (if a1*a2 >= 0)

**Complication:** `cauchy_neg_a1a2_square_le` needs nonneg(b1, f) and nonneg(b2, f). In iszero_im's neg(nx)&&neg(ny) branch, b1/b2 might not be nonneg. Need to establish them from the Ext nonneg_fuel + neg(norm) conditions, or use `nonneg_re_from_neg_im` to derive a different argument.

**Alternative approach:** Don't use `cauchy_neg_a1a2_square_le`. Instead, inline the square_le_implies_le call:
- Establish nonneg(dd*b1*b2) from nonneg_mul(dd, b1*b2) — but b1*b2 might not be nonneg
- Actually: nonneg(dd*b1*b2) can be derived differently. From the Cauchy-Schwarz result Q^2 >= P^2 >= 0 and square_nonneg(Q): Q^2 >= 0, so Q could be anything. But we also have nonneg(dd) and the factor nonneg_fuel conditions.

**Key insight not yet exploited:** In the iszero_im case, `is_zero(im_val)` means `a1*b2 + b1*a2 = 0`. This constrains the relationship between a/b components. Combined with Cauchy-Schwarz, it might simplify things.

## Error 2: nonneg_mul_remaining b1*neg_b2 mixed path

**File:** `dyn_tower_lemmas.rs`, function `lemma_dts_nonneg_mul_remaining`
**Location:** Inside the b1*neg_b2 section, at `if !nonneg(a1*a2)` block, at `nonneg_re_from_neg_im(a2, b2, dd, f)` precondition error.
**Decreases:** (f, 7nat)

**Root cause:** Z3 context pollution. The function is ~800 lines. `!nonneg(b2)` was established ~400 lines earlier at `if b2 { ... }` fall-through but Z3 lost it.

**What works:** The `!b1 && !b2` sub-case inside `if !nonneg(a1*a2)` correctly derives nonneg(a1*a2) -> contradiction. But the `b2 >= 0` sub-case (which is actually unreachable) fails because Z3 thinks it's reachable.

**Why it's unreachable:** We're in the `if !b1` branch (neg(b1)>=0) AND past the `if b2 { ... }` block (without return, so both b2-true and b2-false paths reach here). In the b2-true case, the if-b2 block established b1*neg_b2 >= 0. In the b2-false case (neg(b2)>=0), both a1>=0 and a2>=0 from nonneg_re_from_neg_im, so a1*a2>=0 -> the `if !nonneg(a1*a2)` check fails. So the `if !nonneg(a1*a2)` block is only reached from the b2-true path.

**What the b2-true path needs:** When b2>=0 and neg(b1)>=0 and factor 2 in C3 (neg(a2)>=0): a1>=0 (from nonneg_re_from_neg_im) but a2 might be negative. So a1*a2 might not be nonneg. re_val = a1*a2 + dd*b1*b2. With neg(b1)>=0 and b2>=0: b1*b2 sign depends on b1. dd*b1*b2 = dd*neg(|b1|)*b2 <= 0. So re_val might not be nonneg.

This is the genuinely hard "mixed-norms with mixed b-signs" case. It needs the full Cauchy-Schwarz -> square_le_implies_le chain for the specific sign pattern.

**Possible fix approaches:**
1. **Extract the entire b1*neg_b2 section** (~300 lines) into its own function with explicit !nonneg(b1), !nonneg(b2) preconditions. This gives Z3 a clean context where the early nonneg(a1*a2) establishment from the `if !b2` sub-case propagates correctly.
2. **Early fact establishment:** Already partially done — the `if !b2 { nonneg_re_from_neg_im + nonneg_mul -> nonneg(a1*a2) }` at the fall-through point. This works for the !b2 case but not the b2 case.
3. **Ghost variable threading:** Define `let ghost a1a2_nn = dts_nonneg_fuel(mul(a1,a2), f);` right after establishing it, then assert it before the `if !nonneg(a1*a2)` check 250 lines later. But ghost variables also get lost in polluted contexts.

## Error 3: nonneg_add_closed_fuel (cascading)

Automatically resolves when nonneg_mul_closed verifies (which happens when both iszero_im and nonneg_mul_remaining verify).

## Techniques That Worked

### Ghost equality params (dispatched Z3 context pollution for let-bindings)
```rust
proof fn wrapper(..., nx: T) requires nx == dts_sub(...), nonneg(neg(nx)), ...
```
Call site passes let-binding. Inside wrapper, Z3 uses equality + nonneg for expanded form. Used for `cauchy_nonneg_re_dispatch`.

### Early fact establishment (beat pollution by proving at the if-check point)
Prove downstream consequences immediately while the if-condition is local, not 300 lines later. Used for the `!b1 && !b2` nonneg(a1*a2) establishment.

### C3 elimination via le_antisymmetric
`nonneg_re_from_neg_im`: if neg(b)>=0 and Ext(a,b,d) nonneg, then a>=0. Proof: le_total gives nonneg(b) || nonneg(neg(b)). If nonneg(b): le_antisymmetric -> is_zero(b) -> C3's !is_zero(b) contradicted. So C1/C2 -> nonneg(a).

### cauchy_schwarz_combine (factored transitivity algebra)
Extracted the commute + nonneg_add + sub_add_sub identity from the 270-line assert_by into a clean helper. Reusable for any le_mul chain transitivity step.

### Assert_by scoping for eqv chains
The eqv(nx*ny, re^2) chain (norm_mul + sub_zero simplification) uses ~80 lines of lemma calls. Wrapping in `assert(eqv) by { ... }` scopes these facts and prevents pollution. The nonneg transfer then uses the asserted eqv in the outer scope.

## Techniques That Did NOT Work

### assert(fact) for Z3 hints in polluted functions
Simple `assert(dts_nonneg_fuel(neg_b2, f))` fails in the 700-line function even when the fact was established 37 lines earlier. Z3's context is too large.

### nonneg_or_neg as a universal fix
Calling `nonneg_or_neg(b1, f)` gives the disjunction but Z3 can't resolve which branch without the `!nonneg(b1)` from the if-condition (hundreds of lines away).

### Structural equality for neg(zero) == zero
`dts_neg(dts_zero::<T>()) == dts_zero::<T>()` is NOT structurally true for generic T. Must use `eqv` via `lemma_neg_zero::<T>()` which gives `T::zero().neg().eqv(T::zero())`.

### Removing premature returns to "let proof fall through"
Removing `return;` from a handled case to let it reach a later proof path doesn't work if the later proof has different precondition requirements. The neg(nx)&&neg(ny) case gives nonneg(nx*ny), but the is_zero proof needed nonneg(neg(nx*ny)) — opposite signs!

## Decreases Hierarchy (Final)

| Function | Decreases | Role |
|---|---|---|
| nonneg_mul_closed | (fuel, 0) | Main entry |
| nonneg_add_closed | (fuel, 0) | Addition closure |
| cauchy_schwarz_step | (fuel, 1) | Two le_mul results |
| le_antisymmetric | (fuel, 1) | nonneg(x) + nonneg(neg(x)) -> is_zero(x) |
| nonneg_fuel_congruence | (fuel, 2) | Transfer nonneg through eqv |
| cauchy_schwarz_combine | (fuel, 2) | Commute + nonneg_add + sub_add_sub |
| nonneg_re_from_neg_im | (fuel, 2) | neg(b)>=0 + Ext nonneg -> a>=0 |
| square_le_square | (fuel, 2) | |
| le_mul_nonneg_monotone | (fuel, 2) | |
| nonneg_component_from_ext | (fuel, 3) | nonneg_fuel(Ext) + norm>0 -> nonneg(a) |
| le_transitive_raw | (fuel, 3) | le_mul chain (norm >= 0 direction) |
| le_chain_neg_norms | (fuel, 3) | le_mul chain (norm <= 0 direction) |
| square_le_implies_le | (fuel, 3) | |
| neg_db1b2_case | (fuel, 4) | Congruence + square_le + le_antisymmetric |
| neg_a1a2_square_le | (fuel, 4) | Congruence + square_le -> nonneg(re_val) |
| cauchy_schwarz_is_zero_re | (fuel, 5) | Main Cauchy-Schwarz dispatch (norm >= 0) |
| cauchy_nonneg_re_from_neg_norms | (fuel, 5) | Both norms <= 0 -> nonneg(re_val) |
| cauchy_nonneg_re_dispatch | (fuel, 6) | Clean-context wrapper for Z3 |
| nonneg_mul_iszero_im | (fuel, 6) | Product nonneg when im=0 |
| nonneg_mul_remaining | (fuel, 7) | Product nonneg when im!=0 |

## Files Modified
- `verus-quadratic-extension/src/dyn_tower_lemmas.rs` — all changes are in this file
- New helpers inserted around lines 1830-2400 (after cauchy_nonneg_re_from_neg_norms)
- New `cauchy_schwarz_combine` at line ~10970 (before iszero_im)

## Key Code Locations
- `cauchy_nonneg_re_from_neg_norms`: line ~1654 (both norms <= 0 -> nonneg(re))
- `cauchy_nonneg_re_dispatch`: line ~1836 (ghost param wrapper)
- `nonneg_re_from_neg_im`: line ~1835 (neg(b)>=0 -> a>=0)
- `dd_sq_product_eqv`: line ~1871 (standalone algebra)
- `cauchy_le_chain_neg_norms`: line ~1960 (reversed le_mul chain)
- `cauchy_neg_a1a2_square_le`: line ~2230 (square_le bridge)
- `cauchy_schwarz_combine`: line ~10970 (transitivity helper)
- `nonneg_mul_iszero_im`: line ~11108 (im=0 handler)
- `nonneg_mul_remaining`: line ~11915 (im!=0 handler)
