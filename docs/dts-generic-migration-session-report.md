# DynTowerSpec Generic Migration — Session Report

**Date:** 2026-04-03
**Starting state:** 87 verified, 20 errors (DynTowerSpec hardcoded to Rational)
**Final state:** 96 verified, 3 errors (DynTowerSpec<T: OrderedField>)

## Goal

Migrate DynTowerSpec from hardcoded Rational to generic `T: OrderedField`, enabling:
1. WellFormedDTS<W> wrapper type implementing full OrderedField
2. `lemma_end_to_end<WellFormedDTS<W>>` for free (structural soundness theorem)
3. Dynamic tower as the single canonical path (dropping static L1 pipeline)

## What Was Done

### Phase 1: RuntimeQExtRat Deprecation

Replaced the concrete `RuntimeQExtRat` struct with a type alias to `RuntimeQExtL1<R>` (= `RuntimeQExt<Rational, R, RuntimeRational>`). This is the runtime-level migration — the exec code now goes through generic `RuntimeOrderedFieldOps` trait methods instead of raw `add_spec`/`mul_spec`.

**Changes across 3 crates:**
- **verus-quadratic-extension:** `RuntimeQExtRat` struct → type alias, `View` impl for `RuntimeQExt`, new `zero_with_radicand`/`one_with_radicand` constructors
- **verus-geometry:** `View` impls for `RuntimePoint2/Line2/Circle2/Polygon2`, generified `circle_line`/`circle_circle` exec functions over `RuntimeOrderedFieldOps<V>`
- **verus-2d-constraint-satisfaction:** Concrete type aliases in `runtime/mod.rs`, fixed `copy_rational` imports, removed `<RR>` type params from `mul_exec`/`nonneg_exec`/`lt_exec`, threaded `radicand_rt` through construction pipeline

### Phase 2: DynTowerSpec<T: OrderedField>

The core migration: `DynTowerSpec` becomes `DynTowerSpec<T: OrderedField>` where `T` is the base field at the bottom of the tower.

**Key insight:** When `T` is a type parameter (not a concrete type), `r.neg()` resolves to `AdditiveGroup::neg` (the spec-level trait method) instead of Rational's inherent `proof fn neg`. This eliminates the `add_spec` vs `Ring::add` canonical mismatch that caused 15 of the 20 errors.

**Changes:**
- `dyn_tower.rs`: `DynTowerSpec<T>`, all operations use `T::add`/`T::mul`/`T::neg`/`T::recip`/`T::le`
- `dyn_tower_lemmas.rs` (10800 lines): All 80+ lemmas generic, Rat branches delegate to `T::axiom_*`
- Re-added `Equivalence`/`AdditiveCommutativeMonoid`/`AdditiveGroup` trait impls for `DynTowerSpec<T>`

### Phase 3: Fixing Pre-existing Errors

With the generic migration fixing the canonical mismatch, the remaining errors were pre-existing proof bugs:

| Error | Root Cause | Fix |
|-------|-----------|-----|
| `neg_preserves_is_zero` | Used `eq_implies_eqv(zero.neg(), zero)` — structural eq fails for generic T | Use `lemma_neg_zero::<T>()` from verus-algebra |
| `mul_congruence_right` Rat×Rat | Missing `eqv_symmetric` before `eqv_transitive` | Add `mul_commutative(rb, rc)` for correct direction |
| `neg_sub_swap` | Complex structural recursion for cross-depth cases | Replace entirely with `lemma_neg_sub::<DynTowerSpec<T>>()` (1 line!) |
| `mul_associative` Rat×Rat×Rat | Axiom gives `(a*b)*c ≡ a*(b*c)` but DTS postcondition needs reverse | Add `eqv_symmetric` |
| `norm_mul` `sub_congruence` | Used `sub_congruence(zero, zero, X, Y)` through `DynTowerSpec<T>: AdditiveGroup` | Replace with direct `neg_congruence(X, Y)` |
| `le_antisymmetric_fuel` Rat | Used `.num`/`.den` fields with `nonlinear_arith` | New `lemma_nonneg_both_implies_eqv_zero::<T>` using `le_add_monotone` + `le_congruence` + `le_antisymmetric` |
| `nonneg_mul_iszero_im` same_radicand | Missing `same_radicand(mul(dd_b2_sq, a1_sq), mul(na2_sq, a1_sq))` | Add chain: `dd ~ a2 ~ neg(a2) ~ na2_sq` + `mul_preserves_same_radicand_left` |
| `nonneg_mul_remaining` Point C `neg(neg(b2)) == b2` | Structural `==` fails for generic T (`neg(neg(x))` ≠ x) | Use `lemma_dts_neg_involution(b2)` |
| `nonneg_mul_remaining` Point C same-sign norms | Placeholder `return;` — Cauchy-Schwarz was thought to be needed | **Key discovery:** NOT needed! Both factors C3 (a<0, b>0) → a1*a2≥0 by neg_mul_neg, dd*b1*b2≥0 → nonneg_add |

### Helper Lemma Added

```rust
pub proof fn lemma_nonneg_both_implies_eqv_zero<T: OrderedField>(r: T)
    requires T::zero().le(r), T::zero().le(r.neg()),
    ensures r.eqv(T::zero()),
```

Replaces all Rational-specific `.num`/`.den` reasoning for the "both directions nonneg → zero" pattern. Uses `le_add_monotone` + `add_zero` + `add_inverse` + `le_congruence` + `le_antisymmetric` — purely from OrderedField axioms.

## What Remains

### 3 Remaining Errors (nonneg_mul/add mutual recursion)

All 3 cascade from each other through the mutual recursion between `nonneg_mul_closed_fuel` and `nonneg_add_closed_fuel`:

**Error 1: `nonneg_mul_remaining` — conclude_im precondition**
- Path: `im≥0, neg(re)≥0` → tries `conclude_im` (C3)
- `conclude_im` requires `nonneg(sub(dd*im², re²))` (negative norm)
- Code establishes `nonneg(neg(nx*ny))` via norm product
- Missing: explicit `norm_mul` identity chain + `neg_congruence` to transfer `nonneg(neg(nx*ny))` → `nonneg(sub(dd*im², re²))`
- Fix: ~30 lines of same_radicand boilerplate + norm_mul call + congruence chain
- Risk: function is 600+ lines at 16M rlimit, may need extraction to helper

**Error 2: `nonneg_mul_iszero_im` — Cauchy-Schwarz assertion**
- Cascades from Error 3 (uses `nonneg_add_closed_fuel` in Cauchy-Schwarz transitivity)
- Will auto-fix when Error 3 is fixed

**Error 3: `nonneg_add_closed_fuel` — postcondition**
- Cascades from `nonneg_mul_closed_fuel` → `nonneg_mul_remaining` (Error 1)
- Will auto-fix when Error 1 is fixed

**Conclusion: Fixing Error 1 should cascade-fix all 3.**

### After nonneg_mul is fixed: WellFormedDTS<W>

Architecture (designed but not implemented):

```rust
pub trait RadicandWitness: Sized {
    spec fn radicand_tree() -> DynTowerSpec<T>;
    proof fn axiom_well_formed();
    proof fn axiom_nonneg_radicands();
    proof fn axiom_norm_definite();
    proof fn axiom_same_radicand_self();
}

#[verifier::type_invariant]
pub ghost struct WellFormedDTS<W: RadicandWitness> {
    pub value: DynTowerSpec<T>,
    // invariant: well_formed && same_radicand(value, W::radicand_tree())
    //            && nonneg_radicands && norm_definite
}
```

With the type invariant:
- All `WellFormedDTS<W>` values share `same_radicand` (via transitivity through `W::radicand_tree()`)
- `dts_well_formed`, `dts_nonneg_radicands`, `dts_norm_definite` hold automatically
- These are exactly the preconditions that the standalone DTS lemmas need

**Trait implementations** delegate to existing lemmas:
- **Ring:** `mul_commutative` → `lemma_dts_mul_commutative` (needs well_formed + same_radicand ✓)
- **Field:** `mul_recip_right` → needs new `lemma_dts_recip_mul_right` (not yet written)
- **PartialOrder:** `le_antisymmetric` → `lemma_dts_le_antisymmetric_fuel` (needs norm_definite ✓)
- **OrderedRing:** `le_mul_nonneg_monotone` → `lemma_dts_le_mul_nonneg_monotone_fuel` (needs nonneg_mul_closed — the blocked one)

**Most axioms work now.** Only `le_mul_nonneg_monotone` and `axiom_mul_recip_right` are blocked.

### After WellFormedDTS: Structural Soundness for Free

```
lemma_end_to_end<WellFormedDTS<W>>
```

This gives the structural soundness theorem at the dynamic tower level, meaning:
- If a construction plan is structurally sound at the DTS level
- Then all constraints are satisfied at the DTS level
- Without needing runtime constraint checking as the proof

### Full Roadmap

```
1. Fix conclude_im precondition (Error 1, ~30 lines)
   ↓ cascades fix all 3 errors → 96+ verified, 0 errors
2. Write lemma_dts_recip_mul_right (field inverse axiom)
3. Implement WellFormedDTS<W> with OrderedField (~300 lines)
4. lemma_end_to_end<WellFormedDTS<W>> works for free
5. Bridge: connect execute_all_levels_dyn to spec execution
6. Drop static L1 pipeline entirely
```

## Key Technical Lessons

### Generic T eliminates canonical mismatch
The root cause of 15/20 errors was `Rational::add_spec()` (raw) vs `Ring::add()` (= `add_spec().canonical()`). Making DTS generic over `T: OrderedField` eliminates this because trait methods are the only operations available on `T`.

### Inherent methods shadow trait methods on concrete types
`Rational` has inherent `proof fn add/mul/neg` that shadow the `spec fn` trait methods. When `T = Rational`, `r.neg()` calls the proof-mode inherent method, not the spec-mode trait method. With generic `T`, only the trait method exists. This is why the generic version "just works."

### AdditiveGroup trait impls enable generic lemma reuse
Adding `impl<T: OrderedField> AdditiveGroup for DynTowerSpec<T>` enables calling `verus_algebra::lemmas::additive_group_lemmas::*::<DynTowerSpec<T>>()`. This replaced 30+ lines of structural recursion in `neg_sub_swap` with a single line. Several other lemmas could similarly be delegated to generic algebra lemmas.

### same_radicand boilerplate is the #1 proof cost
Approximately 60% of all proof code in dyn_tower_lemmas.rs is `same_radicand` chain setup (symmetric + transitive calls). The WellFormedDTS wrapper will eliminate this entirely by encoding same_radicand in the type system.

### Point C doesn't need Cauchy-Schwarz
The same-sign norms case (b1≥0, b2≥0, neg(norm_1)≥0, neg(norm_2)≥0) was assumed to need Cauchy-Schwarz to show re_val ≥ 0. In fact, both factors are in C3 (a<0, b>0), so a1*a2 ≥ 0 (neg×neg) and dd*b1*b2 ≥ 0 (all nonneg), giving re_val ≥ 0 by simple nonneg_add. This was a significant simplification of the proof strategy.

### Fuel stabilization is key for ordering proofs
`lemma_dts_nonneg_fuel_stabilize(x, f)` proves `nonneg_fuel(x, f) == nonneg(x)` when `f >= depth(x) + 1`. This bridges between fuel-parametric lemmas (needed for mutual recursion) and the canonical `nonneg` (used in postconditions). Every ordering proof needs this bridge.

## Statistics

| Metric | Before | After |
|--------|--------|-------|
| Verified functions | 87 | 96 |
| Errors | 20 | 3 |
| File: dyn_tower.rs | ~540 lines, Rational | ~460 lines, generic T |
| File: dyn_tower_lemmas.rs | ~10850 lines, Rational | ~10750 lines, generic T |
| Trait impls | Equivalence + Additive only | Same (Ring+ blocked by nonneg_mul) |
| Errors from canonical mismatch | 15 | 0 |
| Errors from missing symmetric | 3 | 0 |
| Errors in nonneg_mul chain | 5 | 3 |
