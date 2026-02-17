import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# End-to-End Example: Anaphora Binding ("John walks. He sleeps.")

This module demonstrates **cross-sentential anaphora resolution** via V3+V4,
proving the complete operational + semantic chain:

1. **V3** (referent intro): Introduce referent `r1` at position `john_PN`
2. **V4** (pronoun bind): Bind pronoun `pr1` to referent `r1` (he → John)
3. **Evidence**: Before V4, evidence for `sleep_V(pr1)` = ⊥; after V4, = real

Working at the `GrammarState` level with explicit patterns, this complements:
- `EveryManWalks.lean` (single quantifier, V1)
- `ScopeAmbiguity.lean` (two quantifiers, V1+V2 scope choice)
-/

namespace Mettapedia.Languages.GF.Examples.AnaphoraBinding

open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.VisibleLayerGFInstance
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2

/-! ## Setup: Patterns and States

The term represents "He sleeps" after V1 NP-replacement:
`PredVP(⊛NPVar(pr1), UseV(sleep_V))`.

The referent position is `john_PN` — where "John" appears syntactically.
V3 introduces the referent, V4 resolves the pronoun to it. -/

/-- The referent position: where "John" appears in the discourse. -/
def john_pos : Pattern := .fvar "john_PN"

/-- The term after V1 replaces the pronoun NP: `PredVP(⊛NPVar(pr1), UseV(sleep_V))` -/
def ana_term : Pattern :=
  .apply "PredVP" [npVar "pr1", .apply "UseV" [.fvar "sleep_V"]]

/-! ## Stage 1: V3 — Referent Introduction

V3 introduces "John" as a discourse referent at position `john_pos`. -/

/-- State 0: term with pronoun placeholder, empty store. -/
def ana_state0 : GrammarState := ⟨ana_term, ∅⟩

/-- State 1: after V3, referent `r1` at `john_pos` recorded in store. -/
def ana_state1 : GrammarState := ⟨ana_term, {StoreAtom.ref "r1" john_pos}⟩

/-- V3 is a valid visible step from state0 to state1. -/
theorem ana_V3_step : VisibleStep gfVisibleCfg ana_state0 ana_state1 := by
  have hfresh : ∀ p, StoreAtom.ref "r1" p ∉ ana_state0.store := by
    simp [ana_state0]
  exact VisibleStep.refIntro "r1" john_pos ana_state0 hfresh

/-! ## Stage 2: V4 — Pronoun Binding

V4 binds pronoun `pr1` to referent `r1`.
Precondition: `ref "r1" john_pos ∈ store` (from V3). -/

/-- State 2: after V4, pronoun `pr1` bound to referent `r1`. -/
def ana_state2 : GrammarState :=
  ⟨ana_term, {StoreAtom.ref "r1" john_pos} + {StoreAtom.bind "pr1" "r1"}⟩

/-- V4 is a valid visible step from state1 to state2. -/
theorem ana_V4_step : VisibleStep gfVisibleCfg ana_state1 ana_state2 := by
  have href : ∃ p, StoreAtom.ref "r1" p ∈ ana_state1.store :=
    ⟨john_pos, Multiset.mem_singleton_self _⟩
  have hfresh : ∀ r', StoreAtom.bind "pr1" r' ∉ ana_state1.store := by
    simp [ana_state1, john_pos]
  exact VisibleStep.pronounBind "pr1" "r1" ana_state1 href hfresh

/-! ## Stage 3: Store Resolution

After V3+V4, the store resolves pronoun `pr1` to position `john_pos`. -/

theorem ana_store_resolves : storeResolves ana_state2.store "pr1" john_pos :=
  ⟨"r1",
   Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)),
   Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))⟩

/-! ## Stage 4: Store Invariants

The V3+V4 chain preserves `functionalBind` and `uniqueRef`. -/

theorem ana_functionalBind_state1 : functionalBind ana_state1.store := by
  intro pr r1 r2 h1 h2
  simp [ana_state1, john_pos] at h1

theorem ana_uniqueRef_state1 : uniqueRef ana_state1.store := by
  intro r p1 p2 h1 h2
  simp [ana_state1, john_pos] at h1 h2
  rw [h1.2, h2.2]

theorem ana_functionalBind_state2 : functionalBind ana_state2.store := by
  intro pr r1 r2 h1 h2
  simp [ana_state2, john_pos] at h1 h2
  rw [h1.2, h2.2]

theorem ana_uniqueRef_state2 : uniqueRef ana_state2.store := by
  intro r p1 p2 h1 h2
  simp [ana_state2, john_pos] at h1 h2
  rw [h1.2, h2.2]

/-! ## Stage 5: Semantic Change — ⊥ to Real Evidence

Before V4, the pronoun `pr1` is unbound: evidence for `sleep_V(pr1)` = ⊥.
After V4, `pr1` resolves to `john_pos`: evidence = `I "sleep_V" [john_pos] term`.

This is the quantitative analogue of the classical insight that unresolved
pronouns have no truth value, while resolved ones do. -/

/-- The full semantic change theorem: V4 transitions evidence from ⊥ to real.

    Uses `V4_post_step_semantic_change` which packages:
    1. Operational: V4 is a `gfReducesFull` step
    2. Pre-state: evidence = ⊥ (unresolved pronoun)
    3. Post-state: evidence = `I "sleep_V" [john_pos] term` (resolved) -/
theorem ana_semantic_change
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) :
    gfReducesFull cfg π ana_state1 ana_state2 ∧
    gsemE2Full cfg π I Dom (.qatom ⟨"sleep_V", [.var "pr1"]⟩) ana_state1 = ⊥ ∧
    gsemE2Full cfg π I Dom (.qatom ⟨"sleep_V", [.var "pr1"]⟩) ana_state2 =
      I "sleep_V" [john_pos] ana_term :=
  V4_post_step_semantic_change (cfg := cfg) (π := π)
    "pr1" "r1" john_pos ana_state1
    (Multiset.mem_singleton_self _)
    (by simp [ana_state1, john_pos])
    ana_functionalBind_state1
    ana_uniqueRef_state1
    "sleep_V" I Dom

/-! ## Stage 6: Base vs Visible Separation

Neither V3 nor V4 is a base step. The base relation preserves the store,
but V3 adds `ref` and V4 adds `bind`. -/

/-- V3 (referent intro) is NOT base-reachable: it changes the store. -/
theorem ana_V3_not_base {π : WorldModelSemantics.TemporalPolicy} :
    ¬ gfReducesBase π ana_state0 ana_state1 :=
  refIntro_not_base (by simp [ana_state0, john_pos])

/-- V4 (pronoun binding) is NOT base-reachable from state1: it changes the store. -/
theorem ana_V4_not_base {π : WorldModelSemantics.TemporalPolicy} :
    ¬ gfReducesBase π ana_state1 ana_state2 :=
  binding_not_base (by simp [ana_state1, john_pos])

/-! ## Summary

```
  Discourse:     "John walks. He sleeps."
  Referent:      john_pos = .fvar "john_PN"
  Term:          PredVP(⊛NPVar(pr1), UseV(sleep_V))

  State 0:       store = ∅
       ↓ V3 (refIntro "r1" john_pos)
  State 1:       store = {ref "r1" john_pos}
       ↓ V4 (pronounBind "pr1" "r1")
  State 2:       store = {ref "r1" john_pos, bind "pr1" "r1"}

  Store resolves: pr1 → r1 → john_pos ✓

  Evidence transition:
    Before V4:   gsemE2Full ... (.qatom ⟨"sleep_V", [.var "pr1"]⟩) = ⊥
    After V4:    gsemE2Full ... (.qatom ⟨"sleep_V", [.var "pr1"]⟩) = I "sleep_V" [john_pos] term

  Base-visible separation:
    V3 not base-reachable ✓ (store changes: ∅ → {ref})
    V4 not base-reachable ✓ (store changes: {ref} → {ref, bind})
```

All steps proven; no proof gaps.
-/

end Mettapedia.Languages.GF.Examples.AnaphoraBinding
