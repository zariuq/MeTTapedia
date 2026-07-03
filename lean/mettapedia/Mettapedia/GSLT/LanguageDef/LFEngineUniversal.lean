/-
# E2b-universal — scaffolding toward `∀ ts, engine agrees with the verified recognizer`  (2026-07-03)

The finite correspondence over the certified engine is done (`LFEngineCorrespondence.lean`).  The
universal statement is a **simulation**: `eval pLF` reproduces the verified `recognize` on *every*
token stream.  Because the engine carries its own step budget (independent of the recognizer's
Peano fuel), the clean universal form quantifies existentially over engine fuel:

    ∀ ts, ∃ N, MatchesVerdict (recognize 64 ts) (eval pLF N (lfrec (encToks ts))).

This file lands the first, presentation-generic brick that makes the `∃ N` form sound: once the
engine reaches a normal form, extra fuel never changes the result (`eval_stable`).  So a simulation
lemma only has to exhibit *some* sufficient fuel per input; stability handles every larger budget.

The remaining crux (the multi-session core) is the per-function simulation
`eval pLF _ ⟦call⟧ = ⟦recognize-step result⟧`, which reasons symbolically about `oneStep` /
`baseReducts` / `matchPat` over `pLF`'s rules (each encoded redex has a unique applicable rule).
That is the honest frontier; it is not yet proved and this file states no unproven theorem about it.

Integrity: 0 sorry / 0 native_decide; `#print axioms` clean.
-/
import MeTTaIL.Semantics.Eval

namespace Mettapedia.GSLT.LanguageDef.LFUniv

open MeTTaIL

/-- A normal term is a fixpoint of the normalizer at *every* fuel (0 included). -/
theorem eval_of_normal (p : Presentation) (w : AST) (hw : oneStep p w = none) :
    ∀ m, eval p m w = w := by
  intro m
  cases m with
  | zero => rfl
  | succ j => simp only [eval, hw]

/-- **Stability / fuel-weakening.** If the normalizer reaches a normal form `v` within `N` steps,
    then any larger budget `N + k` yields the same `v`.  This is what lets the universal
    correspondence be stated with an existential engine budget: prove *some* sufficient fuel, and
    every larger budget agrees. -/
theorem eval_stable (p : Presentation) :
    ∀ (N : Nat) (t v : AST), eval p N t = v → IsNormal p v → ∀ k, eval p (N + k) t = v := by
  intro N
  induction N with
  | zero =>
    intro t v h hnorm k
    simp only [eval] at h
    subst h
    simp only [IsNormal] at hnorm
    simp only [Nat.zero_add]
    exact eval_of_normal p t hnorm k
  | succ n ih =>
    intro t v h hnorm k
    simp only [eval] at h
    cases hstep : oneStep p t with
    | none =>
      rw [hstep] at h
      rw [← h]
      exact eval_of_normal p t hstep (n + 1 + k)
    | some t' =>
      rw [hstep] at h
      have hk : n + 1 + k = (n + k) + 1 := by omega
      rw [hk]
      simp only [eval, hstep]
      exact ih t' v h hnorm k

/-- Corollary in the shape the simulation will use: from a single sufficient fuel `N` reaching a
    normal result `v`, the `∃`-fuel correspondence holds for the whole up-set of budgets. -/
theorem eval_exists_of_reaches (p : Presentation) {t v : AST} {N : Nat}
    (h : eval p N t = v) (hv : IsNormal p v) : ∀ M, N ≤ M → eval p M t = v := by
  intro M hle
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact eval_stable p N t v h hv k

end Mettapedia.GSLT.LanguageDef.LFUniv
