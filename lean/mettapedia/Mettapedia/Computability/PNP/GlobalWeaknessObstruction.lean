import Mettapedia.GSLT.Meredith.WeaknessBridge

/-!
# P vs NP crux: the current weakness bridge is globally constant data

`WeaknessBridge.lean` exports quantities such as `distinctionWeakness ev` and
`nonDistinctionWeakness ev`.  These are global evidence summaries of the whole
finite quotient, not per-state observables.  Therefore any classifier that
factors only through one of these summaries is constant on the whole state
space.

This does not refute a richer GSLT/weakness repair.  It does show that the
currently formalized bridge is too coarse, by itself, to instantiate the
per-instance encoded-family interface used by the switching/ERM route.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.GSLT.Meredith.WeaknessBridge

universe u v

section

variable {U : Type u} [Fintype U] [DecidableEq U]
variable {Q : Type v} [Monoid Q] [CompleteLattice Q]

/-- A predictor factors through the global distinction-weakness summary if it is
obtained by postcomposing that single scalar with some decoder. -/
def FactorsThroughDistinctionWeakness
    (ev : GSLTEvidence U Q) (predict : U → Bool) : Prop :=
  ∃ decode : Q → Bool, ∀ u : U, predict u = decode (distinctionWeakness ev)

/-- Likewise for the global non-distinction weakness. -/
def FactorsThroughNonDistinctionWeakness
    (ev : GSLTEvidence U Q) (predict : U → Bool) : Prop :=
  ∃ decode : Q → Bool, ∀ u : U, predict u = decode (nonDistinctionWeakness ev)

theorem factorsThroughDistinctionWeakness_constant
    (ev : GSLTEvidence U Q)
    {predict : U → Bool}
    (h : FactorsThroughDistinctionWeakness ev predict) :
    ∀ u v : U, predict u = predict v := by
  rcases h with ⟨decode, hdecode⟩
  intro u v
  rw [hdecode u, hdecode v]

theorem factorsThroughNonDistinctionWeakness_constant
    (ev : GSLTEvidence U Q)
    {predict : U → Bool}
    (h : FactorsThroughNonDistinctionWeakness ev predict) :
    ∀ u v : U, predict u = predict v := by
  rcases h with ⟨decode, hdecode⟩
  intro u v
  rw [hdecode u, hdecode v]

theorem not_factorsThroughDistinctionWeakness_of_separates
    (ev : GSLTEvidence U Q)
    {predict : U → Bool} {u v : U}
    (hsep : predict u ≠ predict v) :
    ¬ FactorsThroughDistinctionWeakness ev predict := by
  intro h
  exact hsep (factorsThroughDistinctionWeakness_constant ev h u v)

theorem not_factorsThroughNonDistinctionWeakness_of_separates
    (ev : GSLTEvidence U Q)
    {predict : U → Bool} {u v : U}
    (hsep : predict u ≠ predict v) :
    ¬ FactorsThroughNonDistinctionWeakness ev predict := by
  intro h
  exact hsep (factorsThroughNonDistinctionWeakness_constant ev h u v)

end

end Mettapedia.Computability.PNP
