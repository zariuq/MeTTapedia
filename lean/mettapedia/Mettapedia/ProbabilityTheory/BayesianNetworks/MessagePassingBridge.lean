import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingLiterature
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge

/-!
# Local Bridge from BP Messages to the VE / Valuation Spine

This module packages the first **honest** bridge points between the abstract BP
equations and the existing exact-inference stack:

* unary-factor updates collapse to a local potential evaluation;
* singleton-other-scope ("pairwise leaf") updates collapse to a one-variable
  elimination sum;
* factor beliefs with unit incoming messages are exactly the VE local factors.

These are the reusable local facts we need before stating a full tree-exactness
theorem.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

section LocalBridge

variable {fg : FactorGraph V K}

/-- Local factor used for the pairwise-leaf bridge: the original factor potential
multiplied by the single incoming message from `u`. -/
noncomputable def pairwiseIncomingFactor
    [Mul K] (μ : VarToFactorMsg fg) (f : fg.factors) (u : V) (hu : u ∈ fg.scope f) :
    VariableElimination.Factor (fg := fg) :=
  { scope := fg.scope f
    potential := fun x => fg.potential f x * μ u f (x u hu) }

/-- Unary local BP update: if a factor has no other variables besides `v`,
the factor-to-variable message is just that factor's potential at `x_v`. -/
theorem unaryFactor_localPotential_bridge
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v : V) (hv : v ∈ fg.scope f)
    (hEmpty : (fg.scope f).erase v = ∅) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        (VariableElimination.Factor.ofGraph (fg := fg) f).potential
          (VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv
            (emptyOtherScopeAssign (fg := fg) f v hEmpty)
            x_v) := by
  simpa [VariableElimination.Factor.ofGraph] using
    factorToVarUpdate_eq_potential_of_otherScopeEmpty
      (fg := fg) (μ := μ) (f := f) (v := v) hv hEmpty

/-- Pairwise leaf BP update: if `scope(f) \\ {v} = {u}`, then the
factor-to-variable message is exactly a one-variable elimination sum. -/
theorem pairwiseLeaf_localElimination_bridge
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v u : V) (hv : v ∈ fg.scope f)
    (hSingle : (fg.scope f).erase v = {u}) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        ∑ x_u : fg.stateSpace u,
          (VariableElimination.Factor.ofGraph (fg := fg) f).potential
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              x_v) *
            μ u f x_u := by
  simpa [VariableElimination.Factor.ofGraph] using
    factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := fg) (μ := μ) (f := f) (v := v) (u := u) hv hSingle

/-- Direct VE corollary for the pairwise-leaf case: the factor-to-variable BP
update is exactly the valuation semantics of `Factor.sumOut` applied to the
local factor multiplied by the unique incoming message from `u`. -/
theorem pairwiseLeaf_sumOut_bridge
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v u : V) (hv : v ∈ fg.scope f)
    (hSingle : (fg.scope f).erase v = {u}) :
    ∀ x : fg.FullConfig,
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := pairwiseIncomingFactor (fg := fg) μ f u
            (by
              have huErase : u ∈ (fg.scope f).erase v := by simp [hSingle]
              exact (Finset.mem_erase.mp huErase).2))
          u)).val x =
        factorToVarUpdate (fg := fg) μ f v hv (x v) := by
  classical
  have huErase : u ∈ (fg.scope f).erase v := by
    simp [hSingle]
  have hu : u ∈ fg.scope f := (Finset.mem_erase.mp huErase).2
  have huv : u ≠ v := (Finset.mem_erase.mp huErase).1
  have hvu : v ≠ u := Ne.symm huv
  let ψ : VariableElimination.Factor (fg := fg) :=
    pairwiseIncomingFactor (fg := fg) μ f u hu
  intro x
  have hBridge :=
    congrFun
      (pairwiseLeaf_localElimination_bridge
        (fg := fg) (μ := μ) (f := f) (v := v) (u := u) hv hSingle)
      (x v)
  have hExtend :
      ∀ x_u : fg.stateSpace u,
        VariableElimination.Factor.extend (φ := ψ) u hu (fun w _ => x w) x_u =
          VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv
            (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
            (x v) := by
    intro x_u
    funext w hw
    by_cases hwu : w = u
    · subst w
      calc
        VariableElimination.Factor.extend (φ := ψ) u hu (fun w _ => x w) x_u u hu
            = x_u := by
                simpa using
                  (VariableElimination.Factor.extend_apply_eq
                    (φ := ψ) (v := u) (hv := hu) (x := fun w _ => x w) (val := x_u))
        _ = VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              (x v) u hu := by
                symm
                simpa [singletonOtherScopeAssign, hSingle] using
                  (VariableElimination.Factor.extend_apply_ne
                    (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                    (v := v) (hv := hv)
                    (x := singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                    (val := x v) (u := u) (hu := hu) huv)
    · by_cases hwv : w = v
      · subst w
        calc
          VariableElimination.Factor.extend (φ := ψ) u hu (fun w _ => x w) x_u v hv
              = x v := by
                  simpa using
                    (VariableElimination.Factor.extend_apply_ne
                      (φ := ψ) (v := u) (hv := hu)
                      (x := fun w _ => x w) (val := x_u)
                      (u := v) (hu := hv) hvu)
          _ = VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                v hv
                (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                (x v) v hv := by
                  symm
                  simpa using
                    (VariableElimination.Factor.extend_apply_eq
                      (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                      (v := v) (hv := hv)
                      (x := singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                      (val := x v))
      · have hwScope : w ∈ fg.scope f := by
          simpa [ψ, pairwiseIncomingFactor] using hw
        have hwEraseV : w ∈ (fg.scope f).erase v :=
          Finset.mem_erase.mpr ⟨hwv, hwScope⟩
        have : w = u := by simpa [hSingle] using hwEraseV
        exact (hwu this).elim
  calc
    (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut (φ := ψ) u)).val x
        = ∑ x_u : fg.stateSpace u,
            ψ.potential (VariableElimination.Factor.extend (φ := ψ) u hu (fun w _ => x w) x_u) := by
              simpa [ψ] using
                (VariableElimination.Factor.sumOut_potential_of_mem_full
                  (φ := ψ) (v := u) (hv := hu) x)
    _ = ∑ x_u : fg.stateSpace u,
          fg.potential f
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              (x v)) *
            μ u f x_u := by
          refine Finset.sum_congr rfl ?_
          intro x_u _
          rw [hExtend x_u]
          have hMsg :
              VariableElimination.Factor.extend
                  (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                  v hv
                  (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                  (x v) u hu = x_u := by
                simpa [singletonOtherScopeAssign, hSingle] using
                  (VariableElimination.Factor.extend_apply_ne
                    (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                    (v := v) (hv := hv)
                    (x := singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                    (val := x v) (u := u) (hu := hu) huv)
          simp [ψ, pairwiseIncomingFactor, hMsg]
    _ = factorToVarUpdate (fg := fg) μ f v hv (x v) := by
          symm
          exact hBridge

omit [DecidableEq V] in
/-- Unit-incoming factor beliefs are literally the concrete VE local factors. -/
theorem factorBelief_unit_messages_bridge
    [CommMonoid K] (f : fg.factors) :
    factorBelief (fg := fg) (unitVarToFactor (fg := fg)) f =
      (VariableElimination.Factor.ofGraph (fg := fg) f).potential :=
  factorBelief_unitVarToFactor_eq_ofGraph (fg := fg) f

end LocalBridge

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
