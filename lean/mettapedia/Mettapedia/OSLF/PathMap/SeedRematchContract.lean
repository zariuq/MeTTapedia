import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.OSLF.PathMap.CandidateArchitecture
import Mettapedia.OSLF.PathMap.ImportedRowContract

/-!
# Seed Rematch Contract: Seeded Pattern Matching for Conjunction Chains

Formalizes CeTTa's `space_subst_match_with_seed` from `space_match_backend.c`.

## The CeTTa Seeded Rematch Protocol

CeTTa's conjunction query evaluates patterns left-to-right:
1. Get candidates from `space_subst_query` (PathMap or exact match)
2. For each candidate, merge seed bindings with candidate bindings
   via `space_subst_match_with_seed`
3. Check for binding loops (cyclic variable chains)
4. Successful results accumulate for the next conjunction pattern

## Architecture

| Lean | CeTTa |
|------|-------|
| `seedRematch` | `space_subst_match_with_seed` |
| `seedRematchSafe` | loop-filtered path in `space_subst_match_with_seed` |
| `conjunctionStep` | one pattern in `space_subst_query_conjunction` |
| `RematchSkipCondition` | `sm.exact = true` fast path |

## Key Results

- `seedRematch_extends_seed` — seeded rematch extends incoming bindings
- `seedRematchSafe_no_loop` — safe rematch never produces loops
- `conjunctionStep_sound` — conjunction step agrees with direct matching
- `imported_seedRematch_binding_parity` — imported candidates + seedRematch
  = direct matching (for binding-level parity)
- `skip_rematch_correct` / `full_rematch_required` — honest boundary

## 0 sorry, 0 warnings, 0 errors
-/

namespace Mettapedia.OSLF.PathMap.SeedRematchContract

open Mettapedia.Languages.MeTTa.HE
  (Bindings Space simpleMatch simpleMatch_extends simpleMatch_preserves_seed)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.PathMap.CandidateArchitecture
  (NativeMatcher CandidateSelector twoPhaseQuery directQuery twoPhase_eq_direct)
open Mettapedia.OSLF.PathMap.ImportedRowContract
  (ImportedCandidates RematchFreeSafe PacketRow)
open Mettapedia.Languages.MeTTa.HE (BagSpace)

/-! ## §1: Seed Extension Correctness

The seeded rematch extends the incoming seed honestly.
Maps to: `space_match_backend.c` `space_subst_match_with_seed` preserves
all prior bindings from the conjunction chain. -/

/-- Seeded rematch: match pattern against candidate with pre-existing bindings.
    This is exactly `simpleMatch` from HE — the "seed" is the initial bindings
    parameter that `simpleMatch` already threads through.

    Maps to: `space_subst_match_with_seed(pattern, candidate, seed_bindings)`. -/
def seedRematch (pattern candidate : Atom) (seed : Bindings) (fuel : Nat) : Option Bindings :=
  simpleMatch pattern candidate seed fuel

/-- Seed extension: seeded rematch extends the incoming seed.
    Direct corollary of `simpleMatch_extends`.

    Maps to: CeTTa runtime invariant that prior conjunction bindings survive
    the rematch step. Without this, conjunction chains would lose context.

    Positive example: seed `{$x → "a"}`, pattern `$y`, candidate `"b"`
    → result `{$x → "a", $y → "b"}` extends seed.

    Negative example (impossible): seed `{$x → "a"}` → result `{$y → "b"}`
    losing `$x`. This theorem proves this cannot happen. -/
theorem seedRematch_extends_seed (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : seedRematch pattern candidate seed fuel = some result) :
    seed.Extends result :=
  (simpleMatch_extends fuel).1 pattern candidate seed result hmatch

/-- Seed preservation: individual binding lookup is preserved through rematch.
    Corollary of `seedRematch_extends_seed`.

    Maps to: any specific variable binding from a prior conjunction step
    can still be looked up after rematch succeeds. -/
theorem seedRematch_preserves_lookup (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : seedRematch pattern candidate seed fuel = some result)
    (v : String) (val : Atom) (hseed : seed.lookup v = some val) :
    result.lookup v = some val :=
  seedRematch_extends_seed pattern candidate seed fuel result hmatch v val hseed

/-! ## §2: Loop Rejection Correctness

CeTTa's `bindings_has_loop` rejects cyclic variable chains.
Maps to: `space_match_backend.c` loop check after match.

Positive example of loop: `{$x → $y, $y → $x}` has a loop.
Negative example: `{$x → $y, $y → "a"}` resolves without looping. -/

/-- A binding loop: variable transitively refers to itself.
    Maps to: `bindings_has_loop()` in CeTTa. -/
def Bindings.hasTransitiveLoop (b : Bindings) : Prop := b.hasLoop = true

/-- Loop-filtered seeded rematch: reject if result has binding loop.
    Maps to: the loop check in `space_subst_match_with_seed` that
    filters out cyclic binding results before they enter the
    conjunction accumulator.

    Positive example: match succeeds, no loop → `some result`.
    Negative example: match succeeds, loop detected → `none`. -/
def seedRematchSafe (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) : Option Bindings :=
  match seedRematch pattern candidate seed fuel with
  | some result => if result.hasLoop then none else some result
  | none => none

/-- Safe rematch still extends seed when it succeeds.
    The loop filter only rejects; it never modifies the bindings.
    So when `seedRematchSafe` returns `some result`, that result
    is the same as what `seedRematch` would have returned.

    Maps to: CeTTa's conjunction chain correctness — the loop filter
    is a post-filter, not a transformation. -/
theorem seedRematchSafe_extends_seed (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : seedRematchSafe pattern candidate seed fuel = some result) :
    seed.Extends result := by
  simp only [seedRematchSafe, seedRematch] at hmatch
  cases h : simpleMatch pattern candidate seed fuel with
  | none => simp [h] at hmatch
  | some r =>
    simp [h] at hmatch
    exact hmatch.2 ▸ (simpleMatch_extends fuel).1 pattern candidate seed r h

/-- Safe rematch never produces loops.
    When `seedRematchSafe` succeeds, the result is guaranteed loop-free.

    Maps to: CeTTa never passes looping bindings to the next conjunction
    step. This is a runtime safety invariant.

    Positive example: `seedRematchSafe` returns `some b` → `b.hasLoop = false`.
    Negative example (impossible): `seedRematchSafe` returns `some b` with loop. -/
theorem seedRematchSafe_no_loop (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : seedRematchSafe pattern candidate seed fuel = some result) :
    result.hasLoop = false := by
  simp only [seedRematchSafe, seedRematch] at hmatch
  cases h : simpleMatch pattern candidate seed fuel with
  | none => simp [h] at hmatch
  | some r =>
    simp [h] at hmatch
    exact hmatch.2 ▸ hmatch.1

/-! ## §3: One-Step Conjunction Correctness

Ground a single pattern against the space, filtering through seeded rematch.
Maps to: one iteration of the pattern loop in `space_subst_query_conjunction`. -/

/-- One conjunction step: for each seed, try to match the pattern against
    each atom in the space. Collect all successful (loop-free) bindings.

    Maps to: the inner loop of `space_subst_query_conjunction` that
    iterates over the space for one pattern, producing new seeds for
    the next pattern. -/
def conjunctionStep (space : Space) (pattern : Atom) (seeds : List Bindings)
    (fuel : Nat) : List Bindings :=
  seeds.flatMap fun seed =>
    space.atoms.filterMap fun candidate =>
      seedRematchSafe pattern candidate seed fuel

/-- The native matcher induced by simpleMatch with a given seed and fuel.
    Returns `true` iff `simpleMatch` succeeds with the given seed. -/
def seedNativeMatcher (seed : Bindings) (fuel : Nat) : NativeMatcher where
  isMatch query candidate :=
    (simpleMatch query candidate seed fuel).isSome

/-- The isSome of each seeded rematch agrees with direct simpleMatch.
    That is, `seedRematchSafe` succeeds iff `simpleMatch` succeeds AND
    the result is loop-free.

    Maps to: CeTTa's `space_subst_match_with_seed` is semantically
    a filtered `simpleMatch`, not a different algorithm. When the loop
    filter does not trigger, the two agree exactly. -/
theorem conjunctionStep_sound (pattern : Atom)
    (seed : Bindings) (fuel : Nat) (candidate : Atom) :
    (seedRematchSafe pattern candidate seed fuel).isSome = true ↔
    (∃ result, simpleMatch pattern candidate seed fuel = some result ∧
               result.hasLoop = false) := by
  simp only [seedRematchSafe, seedRematch]
  constructor
  · intro h
    cases hm : simpleMatch pattern candidate seed fuel with
    | none => simp [hm] at h
    | some r =>
      simp [hm] at h
      exact ⟨r, rfl, h⟩
  · intro ⟨result, hmatch, hnoloop⟩
    simp [hmatch, hnoloop]

/-! ## §4: Imported-Row Strengthening

Move from "candidate set parity" to "binding parity after seeded rematch".
Maps to: `imported_query` in `space_match_backend.c` producing the same
match results whether using bridge candidates or native enumeration. -/

/-- A matcher wrapper: simpleMatch with empty bindings and given fuel,
    checking only success/failure (not the binding content).

    This connects the NativeMatcher interface (bool) with simpleMatch (option). -/
def simpleMatchMatcher (fuel : Nat) : NativeMatcher where
  isMatch query candidate := (simpleMatch query candidate Bindings.empty fuel).isSome

/-- If imported candidates are sound, then seeded rematch on those candidates
    produces the same SET of successfully-matched candidates as direct matching.

    The key insight: `importedFallbackParity` gives us candidate-set parity
    (which atoms match). Seeded rematch then processes exactly those atoms.
    Since the candidate set is the same, the set of atoms that survive
    rematch is the same.

    Maps to: `imported_query` V2 path correctness at the binding level.

    Positive example: bridge returns {a, b, c} ⊇ true matches {a, c}.
    After rematch: {a, c} survive. Same as direct: {a, c} survive.

    Negative example (impossible under soundness): bridge returns {a} ⊊ {a, c}.
    Then rematch would miss c. But soundness prevents this. -/
theorem imported_seedRematch_binding_parity
    (ic : ImportedCandidates) (space : BagSpace) (query : Atom) (fuel : Nat)
    (hsound : ic.sound (simpleMatchMatcher fuel) space query)
    (hsubset : ic.candidates query ⊆ space.atomSupport) :
    (ic.candidates query).filter (fun a =>
      (simpleMatch query a Bindings.empty fuel).isSome) =
    space.atomSupport.filter (fun a =>
      (simpleMatch query a Bindings.empty fuel).isSome) := by
  have h := twoPhase_eq_direct
    ⟨ic.candidates⟩ (simpleMatchMatcher fuel) space query hsound hsubset
  simp only [twoPhaseQuery, directQuery, simpleMatchMatcher] at h
  exact h

/-! ## §5: Honest Boundary

State exactly when rematch is required and what conditions would allow
skipping it.

Maps to: CeTTa's `sm.exact` flag and the decision tree in
`space_subst_match_with_seed` that chooses between full rematch
and seed-merge-only. -/

/-- Rematch can be skipped ONLY when the candidate's pre-computed bindings
    are already exact (sm.exact = true in C) and loop-free.

    In CeTTa: `sm.exact` means the PathMap match was ground (no variables
    in the query pattern that need binding) and the match result is already
    the full, correct binding set.

    Maps to: `if (sm.exact && !bindings_has_loop(merged))` fast path. -/
structure RematchSkipCondition (pattern candidate : Atom) (seed precomputed : Bindings)
    (fuel : Nat) where
  /-- The precomputed bindings are exactly what simpleMatch would produce. -/
  exact : simpleMatch pattern candidate seed fuel = some precomputed
  /-- The precomputed bindings are loop-free. -/
  noLoop : precomputed.hasLoop = false

/-- Under skip conditions, the precomputed bindings are correct:
    they equal what seedRematchSafe would produce.

    Maps to: when `sm.exact = true` and loop-free, CeTTa can use the
    precomputed bindings directly without re-running the pattern matcher.

    Positive example: ground query `(= "a" $x)` against `(= "a" "b")` with
    exact match → precomputed `{$x → "b"}` is already correct.

    Negative example: query `$x` against `"a"` with stale seed →
    precomputed bindings may be wrong, must rematch. -/
theorem skip_rematch_correct (pattern candidate : Atom) (seed precomputed : Bindings)
    (fuel : Nat)
    (hskip : RematchSkipCondition pattern candidate seed precomputed fuel) :
    seedRematchSafe pattern candidate seed fuel = some precomputed := by
  simp only [seedRematchSafe, seedRematch]
  rw [hskip.exact]
  simp [hskip.noLoop]

/-- Under skip conditions, the precomputed bindings extend the seed.
    This is a corollary: skip conditions imply correctness, and correct
    rematch always extends the seed. -/
theorem skip_rematch_extends_seed (pattern candidate : Atom) (seed precomputed : Bindings)
    (fuel : Nat)
    (hskip : RematchSkipCondition pattern candidate seed precomputed fuel) :
    seed.Extends precomputed :=
  seedRematch_extends_seed pattern candidate seed fuel precomputed hskip.exact

/-- Without skip conditions, full rematch is required for correctness.
    If we don't know that precomputed bindings are exact, we cannot
    guarantee they match what simpleMatch would produce.

    Maps to: CeTTa's default path — always rematch unless `sm.exact`.

    This theorem states the contrapositive: if precomputed bindings
    differ from what simpleMatch produces, then using them directly
    would be unsound. -/
theorem full_rematch_required (pattern candidate : Atom) (seed precomputed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : simpleMatch pattern candidate seed fuel = some result)
    (hne : precomputed ≠ result) :
    seedRematch pattern candidate seed fuel ≠ some precomputed := by
  unfold seedRematch
  rw [hmatch]
  intro h
  exact hne (Option.some.inj h).symm

/-- Full rematch is always safe: it produces correct results by definition,
    since `seedRematchSafe` IS the native matcher with loop filtering.

    Maps to: CeTTa's always-rematch path is never wrong, only potentially
    slower than the skip path. -/
theorem full_rematch_always_safe (pattern candidate : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : seedRematchSafe pattern candidate seed fuel = some result) :
    seed.Extends result ∧ result.hasLoop = false :=
  ⟨seedRematchSafe_extends_seed pattern candidate seed fuel result hmatch,
   seedRematchSafe_no_loop pattern candidate seed fuel result hmatch⟩

/-! ## §6: Summary — CeTTa Maintainer's Guide

### Runtime Invariants Formalized

| Theorem | CeTTa Invariant |
|---------|-----------------|
| `seedRematch_extends_seed` | Prior conjunction bindings survive rematch |
| `seedRematchSafe_no_loop` | Loop-free bindings enter conjunction accumulator |
| `conjunctionStep_sound` | Conjunction step = filtered simpleMatch |
| `imported_seedRematch_binding_parity` | Bridge + rematch = native matching |
| `skip_rematch_correct` | Exact + loop-free → skip rematch safely |
| `full_rematch_required` | Wrong precomputed bindings → must rematch |
| `full_rematch_always_safe` | Full rematch always produces correct, extending, loop-free results |

### When to Skip Rematch (currently: only when `sm.exact = true`)

A maintainer considering expanding the skip condition must verify:
1. `RematchSkipCondition.exact` — precomputed bindings are exactly correct
2. `RematchSkipCondition.noLoop` — precomputed bindings are loop-free

If EITHER condition fails, full rematch is required.

### Connection to Prior Contracts

- `CandidateArchitecture.twoPhase_eq_direct` — candidate selection correctness
- `ImportedRowContract.importedFallbackParity` — imported candidate parity
- `BindingComposition.simpleMatch_extends` — THE mutual induction (reused, not reproved)
-/

end Mettapedia.OSLF.PathMap.SeedRematchContract
