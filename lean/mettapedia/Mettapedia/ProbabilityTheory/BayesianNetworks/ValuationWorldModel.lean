import Mathlib.Data.Multiset.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.Logic.PLNWorldModel

/-!
# Canonical Semantic WM: Factorization + Marginalization

This module records the **semantic world-model** core as a factorized valuation:

* The WM state is an explicit **factor list**.
* Revision = add factors (at the state level).
* Queries are answered by **exact VE** on that factorization.

This is the canonical “WM = factorized valuation + marginalization” form,
independent of any PLN rule heuristics.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace ValuationWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

section Generic

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

/-- A factorized evidence source (explicit factor list). -/
def WMSource (fg : FactorGraph V K) : Type _ :=
  List (VariableElimination.Factor (fg := fg))

/-- A WM state is a **commutative ledger** of independent factorized sources. -/
def WMState (fg : FactorGraph V K) : Type _ :=
  Multiset (WMSource fg)

/-- Exact unnormalized weight for a constraint set from a WM factorization. -/
noncomputable def weight
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  VariableElimination.weightOfConstraintsList (fg := fg) W constraints

/-- Total unnormalized weight (partition function of the WM state). -/
noncomputable def total
    (W : WMSource fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  weight (fg := fg) (W := W) []

end Generic

/-! ## Evidence extraction for ENNReal factors -/

section ENNReal

variable {V : Type*} [DecidableEq V]
variable {fg : FactorGraph V ENNReal}

/-- Evidence for a single factorized source: pos = constrained weight, neg = remainder. -/
noncomputable def sourceEvidence
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    Evidence :=
  let pos := weight (fg := fg) (W := W) constraints
  let tot := total (fg := fg) (W := W)
  ⟨pos, tot - pos⟩

/-- Evidence for a WM ledger: sum evidence from each independent source. -/
noncomputable def evidence
    (W : WMState fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    Evidence :=
  (W.map (fun src => sourceEvidence (fg := fg) (W := src) constraints)).sum

instance : AddCommMonoid (WMState fg) := by
  dsimp [WMState]
  infer_instance

instance : EvidenceType (WMState fg) :=
  { toAddCommMonoid := inferInstance }

/-- Factorized WM as a `WorldModel` instance (ledger-of-sources semantics). -/
noncomputable instance
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    WorldModel (WMState fg) (List (Σ v : V, fg.stateSpace v)) where
  evidence W q := evidence (fg := fg) (W := W) q
  evidence_add W₁ W₂ q := by
    classical
    let f := fun src => sourceEvidence (fg := fg) (W := src) q
    have h :
        (Multiset.map f (W₁ + W₂)).sum =
          (Multiset.map f W₁).sum + (Multiset.map f W₂).sum := by
      rw [Multiset.map_add, Multiset.sum_add]
    simpa [evidence, f] using h

end ENNReal

end ValuationWorldModel

end Mettapedia.ProbabilityTheory.BayesianNetworks
