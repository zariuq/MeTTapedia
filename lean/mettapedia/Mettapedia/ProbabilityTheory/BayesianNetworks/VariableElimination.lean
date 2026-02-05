import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics

/-!
# Variable Elimination for Discrete Factor Graphs (Exact Query Engine)

This module implements a **variable elimination (VE)** engine for discrete factor graphs.
It is intended as the "exact query answering" backend for the BN world-model sublayer.

Key design choices:
* We work with factor graphs whose potentials are nonnegative (ENNReal),
  but the core algorithm is parametric in `K`.
* Evidence constraints are represented as **indicator factors**.
* Exact answers are computed by summing out all variables in a chosen elimination order.

This is an **exact** algorithm for the declared model class; its complexity is governed
by the elimination order (treewidth).
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace VariableElimination

variable {V K : Type*} [DecidableEq V]

/-! ## Assignments on finite scopes -/

namespace FactorGraph

variable (fg : FactorGraph V K)

/-- An assignment on a finite scope. -/
abbrev Assign (S : Finset V) : Sort _ :=
  ∀ v ∈ S, fg.stateSpace v

noncomputable instance (S : Finset V) [∀ v, Fintype (fg.stateSpace v)] :
    Fintype (FactorGraph.Assign (fg := fg) S) := by
  classical
  refine Fintype.ofEquiv (∀ v : { v : V // v ∈ S }, fg.stateSpace v.val) ?_
  refine {
    toFun := fun f v hv => f ⟨v, hv⟩
    invFun := fun g v => g v.val v.property
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    funext v
    rfl
  · intro g
    funext v hv
    rfl

/-- Restrict an assignment from a larger scope to a smaller one. -/
noncomputable def restrict {S T : Finset V} (h : S ⊆ T)
    (x : FactorGraph.Assign (fg := fg) T) :
    FactorGraph.Assign (fg := fg) S :=
  fun v hv => x v (h hv)

end FactorGraph

/-! ## Factors over scopes -/

/-- A factor with an explicit finite scope. -/
structure Factor (fg : FactorGraph V K) where
  scope : Finset V
  potential : FactorGraph.Assign (fg := fg) scope → K

namespace Factor

variable {fg : FactorGraph V K}

/-- Convert a factor-graph node into a `Factor`. -/
noncomputable def ofGraph (f : fg.factors) : Factor fg :=
  ⟨fg.scope f, fg.potential f⟩

/-- Multiply two factors by merging scopes and multiplying potentials. -/
noncomputable def mul (φ ψ : Factor fg) [Mul K] : Factor fg :=
  let scope := φ.scope ∪ ψ.scope
  have hφ : φ.scope ⊆ scope := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  have hψ : ψ.scope ⊆ scope := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inr hv)
  ⟨scope, fun x =>
      φ.potential (FactorGraph.restrict (fg := fg) (h := hφ) x) *
      ψ.potential (FactorGraph.restrict (fg := fg) (h := hψ) x)⟩

/-- Extend an assignment on `scope \ {v}` with a value for `v`. -/
noncomputable def extend
    (φ : Factor fg) (v : V) (hv : v ∈ φ.scope)
    (x : FactorGraph.Assign (fg := fg) (φ.scope.erase v)) (val : fg.stateSpace v) :
    FactorGraph.Assign (fg := fg) φ.scope :=
  fun u hu =>
    by
      classical
      by_cases h : u = v
      · subst h; exact val
      · exact x u (by
          have : u ∈ φ.scope.erase v := by
            exact Finset.mem_erase.mpr ⟨h, hu⟩
          exact this)

/-! ## Extension lemmas -/

theorem extend_apply_eq (φ : Factor fg) (v : V) (hv : v ∈ φ.scope)
    (x : FactorGraph.Assign (fg := fg) (φ.scope.erase v)) (val : fg.stateSpace v) :
    Factor.extend (φ := φ) v hv x val v hv = val := by
  classical
  simp [Factor.extend]

theorem extend_apply_ne (φ : Factor fg) (v : V) (hv : v ∈ φ.scope)
    (x : FactorGraph.Assign (fg := fg) (φ.scope.erase v)) (val : fg.stateSpace v)
    {u : V} (hu : u ∈ φ.scope) (h : u ≠ v) :
    Factor.extend (φ := φ) v hv x val u hu =
      x u (by exact Finset.mem_erase.mpr ⟨h, hu⟩) := by
  classical
  simp [Factor.extend, h]

/-- Sum out a variable from a factor (exact elimination step).
If the variable is not in scope, return the factor unchanged. -/
noncomputable def sumOut (φ : Factor fg) (v : V) [Fintype (fg.stateSpace v)]
    [AddCommMonoid K] : Factor fg :=
  by
    classical
    by_cases hv : v ∈ φ.scope
    · refine ⟨φ.scope.erase v, ?_⟩
      intro x
      exact
        (Finset.univ : Finset (fg.stateSpace v)).sum (fun val =>
          φ.potential (extend (φ := φ) v hv x val))
    · exact φ

lemma sumOut_scope (φ : Factor fg) (v : V) [Fintype (fg.stateSpace v)]
    [AddCommMonoid K] :
    (Factor.sumOut (φ := φ) v).scope = φ.scope.erase v := by
  classical
  by_cases hv : v ∈ φ.scope
  · simp [Factor.sumOut, hv]
  · simp [Factor.sumOut, hv]

end Factor

/-! ## Variable Elimination -/

variable {fg : FactorGraph V K}

/-! ## Combine-all (valuation algebra view) -/

noncomputable def oneFactor (fg : FactorGraph V K) [One K] : Factor fg :=
  ⟨∅, fun _ => 1⟩

noncomputable def combineAll (fs : List (Factor fg)) [One K] [Mul K] : Factor fg :=
  fs.foldl (fun a b => Factor.mul (fg := fg) a b) (oneFactor (fg := fg))

/-- Sum out a list of variables from a single factor (gold semantics for a combined factor). -/
noncomputable def sumOutAll (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] : Factor fg :=
  order.foldl (fun acc v => Factor.sumOut (φ := acc) v) f

/-! ## Scope bookkeeping for sum-out -/

/-- Erase each variable in a list from a finset (order-insensitive removal). -/
def eraseList (s : Finset V) (order : List V) : Finset V :=
  order.foldl (fun acc v => acc.erase v) s

lemma eraseList_eq_sdiff (s : Finset V) (order : List V) :
    eraseList s order = s \ order.toFinset := by
  classical
  induction order generalizing s with
  | nil =>
      simp [eraseList]
  | cons v vs ih =>
      calc
        eraseList s (v :: vs) = eraseList (s.erase v) vs := by
          simp [eraseList]
        _ = (s.erase v) \ vs.toFinset := by
          simp [ih]
        _ = (s \ vs.toFinset).erase v := by
          simp [Finset.erase_sdiff_comm]
        _ = s \ insert v vs.toFinset := by
          exact (Finset.sdiff_insert (s := s) (t := vs.toFinset) (x := v)).symm
        _ = s \ (List.toFinset (v :: vs)) := by
          simp [List.toFinset_cons]

/-- Multiply a list of factors into a single factor. -/
noncomputable def foldlMul (fs : List (Factor fg)) [Mul K] : Option (Factor fg) :=
  match fs with
  | [] => none
  | f :: fs' => some <| fs'.foldl (fun a b => Factor.mul (fg := fg) a b) f

/-- Eliminate a variable from a list of factors by VE. -/
noncomputable def eliminateVar (fs : List (Factor fg)) (v : V)
    [Fintype (fg.stateSpace v)] [CommSemiring K] : List (Factor fg) :=
  let hit := fs.filter (fun f => v ∈ f.scope)
  let rest := fs.filter (fun f => v ∉ f.scope)
  match foldlMul (fg := fg) hit with
  | none => rest
  | some f =>
      let f' := Factor.sumOut (φ := f) v
      f' :: rest

/-- Eliminate a list of variables in order. -/
noncomputable def eliminateVars (fs : List (Factor fg)) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] : List (Factor fg) :=
  order.foldl (fun acc v => eliminateVar (fg := fg) acc v) fs

/-! ## Singleton-list correctness (combine-then-marginalize base case) -/

theorem eliminateVar_singleton (f : Factor fg) (v : V)
    [Fintype (fg.stateSpace v)] [CommSemiring K] :
    eliminateVar (fg := fg) [f] v = [Factor.sumOut (φ := f) v] := by
  classical
  by_cases hv : v ∈ f.scope
  · simp [eliminateVar, foldlMul, hv, Factor.sumOut]
  · simp [eliminateVar, foldlMul, hv, Factor.sumOut]

theorem eliminateVars_singleton (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :
    eliminateVars (fg := fg) [f] order = [sumOutAll (fg := fg) f order] := by
  classical
  induction order generalizing f with
  | nil =>
      simp [eliminateVars, sumOutAll]
  | cons v vs ih =>
      have h := ih (Factor.sumOut (φ := f) v)
      simpa [eliminateVars, sumOutAll, eliminateVar_singleton] using h

theorem eliminateVars_combineAll (fs : List (Factor fg)) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] [One K] :
    eliminateVars (fg := fg) [combineAll (fg := fg) fs] order =
      [sumOutAll (fg := fg) (combineAll (fg := fg) fs) order] := by
  simpa using eliminateVars_singleton (fg := fg) (f := combineAll (fg := fg) fs) order

/-! ## Algebraic soundness (single-step) -/

theorem sumOut_mul_def_of_mem (φ ψ : Factor fg) (v : V)
    (hv : v ∈ φ.scope ∪ ψ.scope)
    [Fintype (fg.stateSpace v)] [CommSemiring K] :
    Factor.sumOut (φ := Factor.mul (fg := fg) φ ψ) v =
      ⟨(φ.scope ∪ ψ.scope).erase v, fun x =>
        (Finset.univ : Finset (fg.stateSpace v)).sum (fun val =>
          φ.potential
              (FactorGraph.restrict (fg := fg) (h := by
                intro u hu; exact Finset.mem_union.mpr (Or.inl hu))
                (Factor.extend (φ := Factor.mul (fg := fg) φ ψ) v hv x val)) *
          ψ.potential
              (FactorGraph.restrict (fg := fg) (h := by
                intro u hu; exact Finset.mem_union.mpr (Or.inr hu))
                (Factor.extend (φ := Factor.mul (fg := fg) φ ψ) v hv x val)))⟩ := by
  classical
  simp [Factor.sumOut, hv, Factor.mul]

/-! ## Constant evaluation after elimination -/

namespace Factor

variable {fg : FactorGraph V K}

/-- Unique empty assignment for an empty scope. -/
noncomputable def emptyAssign (fg : FactorGraph V K) :
    FactorGraph.Assign (fg := fg) (∅ : Finset V) :=
  by
    intro v hv
    have : False := by
      simp at hv
    exact this.elim

/-- Evaluate a factor with empty scope (requires a proof that the scope is empty). -/
noncomputable def evalConst (φ : Factor fg) (h : φ.scope = ∅) : K :=
  by
    classical
    have hcast : FactorGraph.Assign (fg := fg) φ.scope := by
      simpa [h] using
        (emptyAssign (fg := fg) : FactorGraph.Assign (fg := fg) (∅ : Finset V))
    exact φ.potential hcast

end Factor

/-! ## Constraints as indicator factors -/

namespace Factor

variable {fg : FactorGraph V K}

/-- Indicator factor enforcing a variable to take a specific value. -/
noncomputable def indicator (v : V) (val : fg.stateSpace v)
    [DecidableEq (fg.stateSpace v)] [Zero K] [One K] :
    Factor fg :=
  ⟨{v}, fun x => if x v (by simp) = val then 1 else 0⟩

end Factor

/-- Add a list of equality constraints as indicator factors. -/
noncomputable def addConstraints
    (fs : List (Factor fg))
    (cs : List (Σ v : V, fg.stateSpace v))
    [∀ v, DecidableEq (fg.stateSpace v)] [Zero K] [One K] : List (Factor fg) :=
  cs.foldl (fun acc c => Factor.indicator (fg := fg) c.1 c.2 :: acc) fs

/-! ## Exact query weights via VE -/

lemma sumOutAll_scope (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    (sumOutAll (fg := fg) f order).scope = eraseList f.scope order := by
  classical
  induction order generalizing f with
  | nil =>
      simp [sumOutAll, eraseList]
  | cons v vs ih =>
      have h := ih (Factor.sumOut (φ := f) v)
      simpa [sumOutAll, eraseList, Factor.sumOut_scope] using h

lemma sumOutAll_scope_univ (f : Factor fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    (sumOutAll (fg := fg) f (Finset.univ : Finset V).toList).scope = ∅ := by
  classical
  have h := sumOutAll_scope (fg := fg) f (Finset.univ : Finset V).toList
  have h' : f.scope \ (Finset.univ : Finset V) = (∅ : Finset V) := by
    ext u; simp
  simpa [eraseList_eq_sdiff, h'] using h

/-- Build the list of factors from a factor graph. -/
noncomputable def factorsOfGraph (fg : FactorGraph V K) [Fintype fg.factors] :
    List (Factor fg) :=
  (Finset.univ : Finset fg.factors).toList.map (Factor.ofGraph (fg := fg))

/-! ## List-based semantic form (factorization-as-state) -/

/-- Exact unnormalized weight for a constraint set, starting from an explicit factor list.
This is the canonical “WM = factorization” semantic form. -/
noncomputable def weightOfConstraintsList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  let fs' := addConstraints (fg := fg) fs constraints
  let order := (Finset.univ : Finset V).toList
  let f := sumOutAll (fg := fg) (combineAll (fg := fg) fs') order
  have hscope : f.scope = ∅ := by
    simpa using sumOutAll_scope_univ (fg := fg) (f := combineAll (fg := fg) fs')
  Factor.evalConst (fg := fg) f hscope

/-- Exact unnormalized weight for a constraint set (semantic combine+sum-out form). -/
noncomputable def weightOfConstraints
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] : K :=
  weightOfConstraintsList (fg := fg) (factorsOfGraph (fg := fg)) constraints

theorem weightOfConstraints_eq_list
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] :
    weightOfConstraints (fg := fg) constraints =
      weightOfConstraintsList (fg := fg) (factorsOfGraph (fg := fg)) constraints := by
  rfl

/-! ## BN queries via VE (prop/link) -/

namespace BayesianNetwork

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.DiscreteCPT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)

/-- Exact probability of an event `v = val` in a discrete BN (semantic factor-graph form). -/
noncomputable def propProbVE (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : ENNReal :=
  by
    classical
    let fg := toFactorGraph (bn := bn) cpt
    have instFactors : Fintype fg.factors := by
      dsimp [fg, toFactorGraph]
      infer_instance
    have instState : ∀ v, Fintype (fg.stateSpace v) := by
      intro v
      simpa [fg, toFactorGraph] using (inferInstance : Fintype (bn.stateSpace v))
    have instDecEq : ∀ v, DecidableEq (fg.stateSpace v) := by
      intro v
      simpa [fg, toFactorGraph] using (inferInstance : DecidableEq (bn.stateSpace v))
    letI : Fintype fg.factors := instFactors
    letI : ∀ v, Fintype (fg.stateSpace v) := instState
    letI : ∀ v, DecidableEq (fg.stateSpace v) := instDecEq
    let num := weightOfConstraints (fg := fg) [⟨v, val⟩]
    let den := weightOfConstraints (fg := fg) []
    exact if den = 0 then 0 else num / den

/-- Exact conditional probability `P(B = valB | A = valA)` (semantic factor-graph form). -/
noncomputable def linkProbVE (cpt : bn.DiscreteCPT)
    (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : ENNReal :=
  by
    classical
    let fg := toFactorGraph (bn := bn) cpt
    have instFactors : Fintype fg.factors := by
      dsimp [fg, toFactorGraph]
      infer_instance
    have instState : ∀ v, Fintype (fg.stateSpace v) := by
      intro v
      simpa [fg, toFactorGraph] using (inferInstance : Fintype (bn.stateSpace v))
    have instDecEq : ∀ v, DecidableEq (fg.stateSpace v) := by
      intro v
      simpa [fg, toFactorGraph] using (inferInstance : DecidableEq (bn.stateSpace v))
    letI : Fintype fg.factors := instFactors
    letI : ∀ v, Fintype (fg.stateSpace v) := instState
    letI : ∀ v, DecidableEq (fg.stateSpace v) := instDecEq
    let num := weightOfConstraints (fg := fg) [⟨a, valA⟩, ⟨b, valB⟩]
    let den := weightOfConstraints (fg := fg) [⟨a, valA⟩]
    exact if den = 0 then 0 else num / den

end BayesianNetwork

end VariableElimination

end Mettapedia.ProbabilityTheory.BayesianNetworks
