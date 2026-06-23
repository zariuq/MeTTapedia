import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationAlgebra

/-!
# Variable Elimination for Discrete Factor Graphs (Exact Query Engine)

This module implements a **variable elimination (VE)** engine for discrete factor graphs.
It is intended as the "exact query answering" backend for the BN world-model sublayer.

Key design choices:
* We work with factor graphs whose potentials are nonnegative (ENNReal),
  but the core algorithm is parametric in `K`.
* BinaryEvidence constraints are represented as **indicator factors**.
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

/-- Restrict a full configuration to a finite scope. -/
noncomputable def fullAssign (x : fg.FullConfig) (S : Finset V) :
    FactorGraph.Assign (fg := fg) S :=
  fun v _ => x v

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

/-- Sum a factor over all assignments to its declared scope. -/
noncomputable def totalWeight (φ : Factor fg)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] : K :=
  ∑ x : FactorGraph.Assign (fg := fg) φ.scope, φ.potential x

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

/-- A unary neutral factor that only serves to keep a variable in scope during elimination. -/
noncomputable def unitVar (v : V) [One K] : Factor fg :=
  ⟨{v}, fun _ => 1⟩

omit [DecidableEq V] in
@[simp] theorem unitVar_scope (v : V) [One K] :
    (unitVar (fg := fg) v).scope = {v} := rfl

omit [DecidableEq V] in
@[simp] theorem unitVar_potential (v : V) [One K]
    (x : FactorGraph.Assign (fg := fg) ({v} : Finset V)) :
    (unitVar (fg := fg) v).potential x = 1 := rfl

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

lemma sumOut_def (φ : Factor fg) (v : V) [Fintype (fg.stateSpace v)]
    [AddCommMonoid K] :
    Factor.sumOut (φ := φ) v =
      (if hv : v ∈ φ.scope then
          ⟨φ.scope.erase v, fun x =>
              (Finset.univ : Finset (fg.stateSpace v)).sum
                (fun val => φ.potential (extend (φ := φ) v hv x val))⟩
        else φ) := by
  classical
  by_cases hv : v ∈ φ.scope
  · simp [Factor.sumOut, hv]
  · simp [Factor.sumOut, hv]

lemma sumOut_scope (φ : Factor fg) (v : V) [Fintype (fg.stateSpace v)]
    [AddCommMonoid K] :
    (Factor.sumOut (φ := φ) v).scope = φ.scope.erase v := by
  classical
  by_cases hv : v ∈ φ.scope
  · simp [Factor.sumOut, hv]
  · simp [Factor.sumOut, hv]

noncomputable def eraseAssignEquiv (φ : Factor fg) (v : V) (hv : v ∈ φ.scope) :
    (FactorGraph.Assign (fg := fg) (φ.scope.erase v) × fg.stateSpace v) ≃
      FactorGraph.Assign (fg := fg) φ.scope where
  toFun p := Factor.extend (φ := φ) v hv p.1 p.2
  invFun x :=
    (fun u hu => x u (Finset.mem_of_mem_erase hu), x v hv)
  left_inv p := by
    rcases p with ⟨x, val⟩
    refine Prod.ext ?_ ?_
    · funext u hu
      simpa using
        Factor.extend_apply_ne (φ := φ) (v := v) (hv := hv) (x := x) (val := val)
          (hu := Finset.mem_of_mem_erase hu) (h := Finset.ne_of_mem_erase hu)
    · simpa using Factor.extend_apply_eq (φ := φ) (v := v) (hv := hv) (x := x) (val := val)
  right_inv x := by
    funext u hu
    classical
    by_cases h : u = v
    · subst h
      simp [Factor.extend]
    · simp [Factor.extend, h]

theorem totalWeight_sumOut (φ : Factor fg) (v : V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    totalWeight (φ := Factor.sumOut (φ := φ) v) = totalWeight (φ := φ) := by
  classical
  by_cases hv : v ∈ φ.scope
  · unfold totalWeight
    rw [Factor.sumOut_def]
    let A : (v ∈ φ.scope) → Factor fg := fun hv' =>
      ⟨φ.scope.erase v, fun x =>
        (Finset.univ : Finset (fg.stateSpace v)).sum
          (fun val => φ.potential (Factor.extend (φ := φ) v hv' x val))⟩
    have hif : (if hv' : v ∈ φ.scope then A hv' else φ) = A hv := by
      by_cases hv' : v ∈ φ.scope
      · simp [A, hv']
      · exact (False.elim (hv' hv))
    rw [hif]
    simp [A]
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (eraseAssignEquiv (φ := φ) v hv)
      (fun p => φ.potential (Factor.extend (φ := φ) v hv p.1 p.2))
      (fun x => φ.potential x)
      (by
        intro p
        rfl)
  · unfold totalWeight
    rw [Factor.sumOut_def]
    let A : (v ∈ φ.scope) → Factor fg := fun hv' =>
      ⟨φ.scope.erase v, fun x =>
        (Finset.univ : Finset (fg.stateSpace v)).sum
          (fun val => φ.potential (Factor.extend (φ := φ) v hv' x val))⟩
    have hif : (if hv' : v ∈ φ.scope then A hv' else φ) = φ := by
      by_cases hv' : v ∈ φ.scope
      · exact (False.elim (hv hv'))
      · simp [A, hv']
    rw [hif]

end Factor

/-! ## Variable Elimination -/

variable {fg : FactorGraph V K}

/-! ## Combine-all (valuation algebra view) -/

noncomputable def oneFactor (fg : FactorGraph V K) [One K] : Factor fg :=
  ⟨∅, fun _ => 1⟩

noncomputable def combineAll (fs : List (Factor fg)) [One K] [Mul K] : Factor fg :=
  fs.foldr (fun f acc => Factor.mul (fg := fg) f acc) (oneFactor (fg := fg))


/-- Sum out a list of variables from a single factor (gold semantics for a combined factor). -/
noncomputable def sumOutAll (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] : Factor fg :=
  order.foldl (fun acc v => Factor.sumOut (φ := acc) v) f

theorem totalWeight_sumOutAll (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    Factor.totalWeight (φ := sumOutAll (fg := fg) f order) = Factor.totalWeight (φ := f) := by
  classical
  induction order generalizing f with
  | nil =>
      simp [sumOutAll]
  | cons v vs ih =>
      simpa [sumOutAll, Factor.totalWeight_sumOut] using
        ih (f := Factor.sumOut (φ := f) v)

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

/-- Eliminate a variable from a list of factors by VE. -/
noncomputable def eliminateVar (fs : List (Factor fg)) (v : V)
    [Fintype (fg.stateSpace v)] [CommSemiring K] : List (Factor fg) :=
  let hit := fs.filter (fun f => v ∈ f.scope)
  let rest := fs.filter (fun f => v ∉ f.scope)
  match hit with
  | [] => rest
  | _ =>
      let f := combineAll (fg := fg) hit
      let f' := Factor.sumOut (φ := f) v
      f' :: rest

/-- Eliminate a list of variables in order. -/
noncomputable def eliminateVars (fs : List (Factor fg)) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] : List (Factor fg) :=
  order.foldl (fun acc v => eliminateVar (fg := fg) acc v) fs

/-! ## Bridge to valuation algebra (full-config semantics) -/

namespace Factor

variable {fg : FactorGraph V K}

local notation "β" => (fun v : V => fg.stateSpace v)

noncomputable def toValuation (φ : Factor fg) : Valuation V β K :=
  ⟨φ.scope, fun x => φ.potential (fun v _ => x v)⟩

omit [DecidableEq V] in
lemma restrict_full (x : FullConfig V β) {S T : Finset V} (h : S ⊆ T) :
    FactorGraph.restrict (fg := fg) (h := h) (fun v _ => x v) =
      (fun v _ => x v) := by
  funext v _
  rfl

omit [DecidableEq V] in
lemma toValuation_respectsScope (φ : Factor fg) :
    RespectsScope (toValuation (φ := φ)) := by
  intro x y hxy
  have hassign : (fun v (hv : v ∈ φ.scope) => x v) =
      (fun v (hv : v ∈ φ.scope) => y v) := by
    funext v hv
    exact hxy v hv
  simp [toValuation, hassign]

lemma toValuation_mul (φ ψ : Factor fg) [Mul K] :
    toValuation (φ := Factor.mul (fg := fg) φ ψ) =
      Mettapedia.ProbabilityTheory.BayesianNetworks.combine
        (φ := toValuation (φ := φ)) (ψ := toValuation (φ := ψ)) := by
  apply Valuation.ext
  · rfl
  · intro x
    simp [toValuation, Factor.mul, Mettapedia.ProbabilityTheory.BayesianNetworks.combine,
      restrict_full]

omit [DecidableEq V] in
lemma toValuation_oneFactor [One K] :
    toValuation (φ := oneFactor fg) =
      oneValuation V β K := by
  apply Valuation.ext
  · rfl
  · intro x
    simp [toValuation, oneFactor, oneValuation]

lemma sumOut_potential_of_mem_full (φ : Factor fg) (v : V)
    [Fintype (fg.stateSpace v)] [AddCommMonoid K] (hv : v ∈ φ.scope)
    (x : FullConfig V β) :
    (toValuation (φ := Factor.sumOut (φ := φ) v)).val x =
      ∑ val : fg.stateSpace v,
        φ.potential (Factor.extend (φ := φ) v hv (fun u _ => x u) val) := by
  classical
  dsimp [toValuation]
  rw [sumOut_def]
  let A : (v ∈ φ.scope) → Factor fg := fun hv' =>
    ⟨φ.scope.erase v, fun x =>
        (Finset.univ : Finset (fg.stateSpace v)).sum
          (fun val => φ.potential (Factor.extend (φ := φ) v hv' x val))⟩
  have hif : (if hv' : v ∈ φ.scope then A hv' else φ) = A hv := by
    by_cases hv' : v ∈ φ.scope
    · simp [hv']
    · exact (False.elim (hv' hv))
  rw [hif]

lemma sumOut_potential_of_not_mem_full (φ : Factor fg) (v : V)
    [Fintype (fg.stateSpace v)] [AddCommMonoid K] (hv : v ∉ φ.scope)
    (x : FullConfig V β) :
    (toValuation (φ := Factor.sumOut (φ := φ) v)).val x =
      φ.potential (fun u _ => x u) := by
  classical
  dsimp [toValuation]
  rw [sumOut_def]
  let A : (v ∈ φ.scope) → Factor fg := fun hv' =>
    ⟨φ.scope.erase v, fun x =>
        (Finset.univ : Finset (fg.stateSpace v)).sum
          (fun val => φ.potential (Factor.extend (φ := φ) v hv' x val))⟩
  have hif : (if hv' : v ∈ φ.scope then A hv' else φ) = φ := by
    by_cases hv' : v ∈ φ.scope
    · exact (False.elim (hv hv'))
    · simp [hv']
  rw [hif]

lemma toValuation_sumOut (φ : Factor fg) (v : V)
    [Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    toValuation (φ := Factor.sumOut (φ := φ) v) =
      Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
        (φ := toValuation (φ := φ)) v := by
  classical
  by_cases hv : v ∈ φ.scope
  · apply Valuation.ext
    · simp [toValuation, Factor.sumOut, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hv]
    · intro x
      have hassign :
          ∀ val : fg.stateSpace v,
            (fun u hu => Factor.extend (φ := φ) v hv (fun u hu => x u) val u hu) =
              (fun u hu => update x v val u) := by
            intro val
            funext u hu
            by_cases h : u = v
            · subst h
              simp [Factor.extend, update]
            · simp [Factor.extend, update, h]
      calc
        (toValuation (φ := Factor.sumOut (φ := φ) v)).val x =
            (∑ val : fg.stateSpace v,
              φ.potential (Factor.extend (φ := φ) v hv (fun u hu => x u) val)) := by
                simpa using
                  (sumOut_potential_of_mem_full (φ := φ) (v := v) (hv := hv) x)
        _ = ∑ val : fg.stateSpace v,
              φ.potential (fun u hu => update x v val u) := by
                refine Finset.sum_congr rfl ?_
                intro val _
                simp [hassign val]
        _ = (Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
              (φ := toValuation (φ := φ)) v).val x := by
                simp [toValuation, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hv]
  · apply Valuation.ext
    · simp [toValuation, Factor.sumOut, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hv]
    · intro x
      calc
        (toValuation (φ := Factor.sumOut (φ := φ) v)).val x =
            φ.potential (fun u hu => x u) := by
              simpa using
                (sumOut_potential_of_not_mem_full (φ := φ) (v := v) (hv := hv) x)
        _ = (Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
              (φ := toValuation (φ := φ)) v).val x := by
              simp [toValuation, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hv]

lemma toValuation_combineAll (fs : List (Factor fg)) [One K] [Mul K] :
    toValuation (φ := combineAll fs) =
      Mettapedia.ProbabilityTheory.BayesianNetworks.combineAll
        (fs.map fun f => toValuation (φ := f)) := by
  classical
  induction fs with
  | nil =>
      simp [combineAll, toValuation_oneFactor,
        Mettapedia.ProbabilityTheory.BayesianNetworks.combineAll, oneValuation]
  | cons f fs ih =>
      calc
        toValuation (φ := combineAll (f :: fs)) =
            Mettapedia.ProbabilityTheory.BayesianNetworks.combine
              (φ := toValuation (φ := f))
              (ψ := toValuation (φ := combineAll fs)) := by
                simp [combineAll, toValuation_mul]
        _ =
            Mettapedia.ProbabilityTheory.BayesianNetworks.combine
              (φ := toValuation (φ := f))
              (ψ := Mettapedia.ProbabilityTheory.BayesianNetworks.combineAll
                (fs.map fun g => toValuation (φ := g))) := by
                simp [ih]
        _ =
            Mettapedia.ProbabilityTheory.BayesianNetworks.combineAll
              (toValuation (φ := f) :: fs.map fun g => toValuation (φ := g)) := by
                simp [Mettapedia.ProbabilityTheory.BayesianNetworks.combineAll]

lemma toValuation_sumOutAll (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    toValuation (φ := sumOutAll f order) =
      Mettapedia.ProbabilityTheory.BayesianNetworks.sumOutAll
        (φ := toValuation (φ := f)) order := by
  classical
  induction order generalizing f with
  | nil =>
      simp [sumOutAll, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOutAll]
  | cons v vs ih =>
      simpa [sumOutAll, Mettapedia.ProbabilityTheory.BayesianNetworks.sumOutAll,
        toValuation_sumOut] using ih (f := Factor.sumOut (φ := f) v)

end Factor

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

/-! ## Exact query weights (semantic form) -/

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

/-- Equality constraints turned into explicit unary indicator factors. -/
noncomputable def constraintFactors
    (constraints : List (Σ v : V, fg.stateSpace v))
    [∀ v, DecidableEq (fg.stateSpace v)] [Zero K] [One K] : List (Factor fg) :=
  constraints.map (fun c => Factor.indicator (fg := fg) c.1 c.2)

/-- Neutral unary factors on every variable, used to keep scope equal to `univ`
for fully operational elimination statements. -/
noncomputable def coveringFactors (fg : FactorGraph V K)
    [Fintype V] [One K] : List (Factor fg) :=
  (Finset.univ : Finset V).toList.map (fun v => Factor.unitVar (fg := fg) v)

/-- The explicit factor list used by the operational VE query surface:
constraint indicators, user factors, and neutral scope-covering unary factors. -/
noncomputable def veFactorList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, DecidableEq (fg.stateSpace v)] [Zero K] [One K] : List (Factor fg) :=
  constraintFactors (fg := fg) constraints ++ fs ++ coveringFactors (fg := fg)

lemma mem_combineAll_scope_of_mem [One K] [Mul K] :
    ∀ {fs : List (Factor fg)} {φ : Factor fg},
      φ ∈ fs → ∀ {v : V}, v ∈ φ.scope → v ∈ (combineAll (fg := fg) fs).scope
  | [], _, hmem, _, _ => by
      simp at hmem
  | ψ :: fs, φ, hmem, v, hv => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Finset.mem_union.mpr <| Or.inl hv
      · exact Finset.mem_union.mpr <| Or.inr (mem_combineAll_scope_of_mem htail hv)

omit [DecidableEq V] in
noncomputable def assignUnivEquivFullConfig
    (fg : FactorGraph V K) [Fintype V] :
    FactorGraph.Assign (fg := fg) (Finset.univ : Finset V) ≃ fg.FullConfig where
  toFun x v := x v (by simp)
  invFun x v _ := x v
  left_inv x := by
    funext v hv
    rfl
  right_inv x := by
    funext v
    rfl

namespace Factor

noncomputable def fullConfigWeightSum (φ : Factor fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] : K := by
  classical
  letI : Fintype fg.FullConfig := by
    dsimp [FactorGraph.FullConfig]
    infer_instance
  exact ∑ x : fg.FullConfig, φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope)

theorem totalWeight_eq_evalConst_of_scope_empty (φ : Factor fg)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] (h : φ.scope = ∅) :
    totalWeight (φ := φ) = evalConst (φ := φ) h := by
  classical
  cases φ with
  | mk scope potential =>
      cases h
      letI : Unique (FactorGraph.Assign (fg := fg) (∅ : Finset V)) := {
        default := emptyAssign fg
        uniq := by
          intro x
          funext v hv
          simp at hv }
      have hdefault : (default : FactorGraph.Assign (fg := fg) (∅ : Finset V)) = emptyAssign fg := by
        exact Unique.uniq _ _
      simp [totalWeight, evalConst, hdefault]

theorem totalWeight_eq_fullConfigSum_of_scope_univ (φ : Factor fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K]
    (h : φ.scope = Finset.univ) :
    totalWeight (φ := φ) = fullConfigWeightSum (φ := φ) := by
  classical
  cases φ with
  | mk scope potential =>
      cases h
      unfold totalWeight fullConfigWeightSum
      letI : Fintype fg.FullConfig := by
        dsimp [FactorGraph.FullConfig]
        infer_instance
      apply Fintype.sum_equiv (assignUnivEquivFullConfig (fg := fg))
      · intro x
        rfl

end Factor

omit [DecidableEq V] in
lemma restrict_fullAssign {S T : Finset V} (h : S ⊆ T) (x : fg.FullConfig) :
    FactorGraph.restrict (fg := fg) (h := h) (FactorGraph.fullAssign (fg := fg) x T) =
      FactorGraph.fullAssign (fg := fg) x S := by
  funext v hv
  rfl

lemma combineAll_potential_fullAssign_listProd (fs : List (Factor fg))
    [One K] [Mul K] (x : fg.FullConfig) :
    (combineAll (fg := fg) fs).potential
        (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope) =
      (fs.map (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
  classical
  induction fs with
  | nil =>
      simp [combineAll, oneFactor]
  | cons φ fs ih =>
      calc
        (combineAll (fg := fg) (φ :: fs)).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) (φ :: fs)).scope)
            =
            (Factor.mul (fg := fg) φ (combineAll (fg := fg) fs)).potential
              (FactorGraph.fullAssign (fg := fg) x
                (Factor.mul (fg := fg) φ (combineAll (fg := fg) fs)).scope) := by
              rfl
        _ =
            φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope) *
              (combineAll (fg := fg) fs).potential
                (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope) := by
              simp [Factor.mul, restrict_fullAssign]
        _ =
            φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope) *
              (fs.map (fun ψ => ψ.potential (FactorGraph.fullAssign (fg := fg) x ψ.scope))).prod := by
              simp [ih]

omit [DecidableEq V] in
lemma constraintFactors_product_fullAssign
    (constraints : List (Σ v : V, fg.stateSpace v))
    (x : fg.FullConfig)
    [∀ v, DecidableEq (fg.stateSpace v)] [CommSemiring K] :
    ((constraintFactors (fg := fg) constraints).map
      (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope))).prod =
      if ∀ c ∈ constraints, x c.1 = c.2 then 1 else 0 := by
  classical
  induction constraints with
  | nil =>
      simp [constraintFactors]
  | cons c cs ih =>
      by_cases hc : x c.1 = c.2
      · have hsat :
          (∀ q ∈ c :: cs, x q.1 = q.2) ↔ ∀ q ∈ cs, x q.1 = q.2 := by
          constructor
          · intro h q hq
            exact h q (by simp [hq])
          · intro h q hq
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact hc
            · exact h q hq'
        simpa [constraintFactors, Factor.indicator, FactorGraph.fullAssign, hc, hsat] using ih
      · have hsat : ¬ ∀ q ∈ c :: cs, x q.1 = q.2 := by
          intro h
          exact hc (h c (by simp))
        simp [constraintFactors, Factor.indicator, FactorGraph.fullAssign, hc]

omit [DecidableEq V] in
lemma coveringFactors_product_fullAssign
    (x : fg.FullConfig)
    [Fintype V] [CommSemiring K] :
    ((coveringFactors (fg := fg)).map
      (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope))).prod = 1 := by
  classical
  simp [coveringFactors]

lemma veFactorList_scope_univ
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, DecidableEq (fg.stateSpace v)] [Zero K] [One K] [Mul K] :
    (combineAll (fg := fg) (veFactorList (fg := fg) fs constraints)).scope = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    simp
  · intro _
    have hcover : Factor.unitVar (fg := fg) v ∈ coveringFactors (fg := fg) := by
      unfold coveringFactors
      apply List.mem_map.mpr
      exact ⟨v, by simp, rfl⟩
    have hmem : Factor.unitVar (fg := fg) v ∈ veFactorList (fg := fg) fs constraints := by
      unfold veFactorList
      simp [hcover]
    exact mem_combineAll_scope_of_mem (fg := fg) hmem (by simp [Factor.unitVar])

lemma veFactorList_potential_fullAssign
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    (x : fg.FullConfig)
    [Fintype V] [∀ v, DecidableEq (fg.stateSpace v)] [CommSemiring K] :
    (combineAll (fg := fg) (veFactorList (fg := fg) fs constraints)).potential
        (FactorGraph.fullAssign (fg := fg) x
          (combineAll (fg := fg) (veFactorList (fg := fg) fs constraints)).scope) =
      if ∀ c ∈ constraints, x c.1 = c.2 then
        (combineAll (fg := fg) fs).potential
          (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
      else 0 := by
  classical
  rw [combineAll_potential_fullAssign_listProd (fg := fg)
    (fs := veFactorList (fg := fg) fs constraints) x]
  by_cases hs : ∀ c ∈ constraints, x c.1 = c.2
  · simp [veFactorList, List.map_append, List.prod_append,
      constraintFactors_product_fullAssign, coveringFactors_product_fullAssign,
      combineAll_potential_fullAssign_listProd]
  · simp [veFactorList, List.map_append, List.prod_append,
      constraintFactors_product_fullAssign, coveringFactors_product_fullAssign, hs]

/-! ## List-based semantic form (factorization-as-state) -/

/-- Exact unnormalized weight for a constraint set, starting from an explicit factor list.
This is the canonical “WM = factorization” semantic form: sum the joint potential
over all configurations that satisfy the constraints. -/
noncomputable def weightOfConstraintsList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
by
  classical
  letI : Fintype fg.FullConfig := by
    dsimp [FactorGraph.FullConfig]
    infer_instance
  let f := combineAll (fg := fg) fs
  let cfgs : Finset (fg.FullConfig) := Finset.univ
  -- A configuration satisfies all constraints if it agrees on each constraint.
  let satisfies : fg.FullConfig → Prop :=
    fun x => ∀ c ∈ constraints, x c.1 = c.2
  exact
    cfgs.sum (fun x =>
      if satisfies x then
        f.potential (FactorGraph.fullAssign (fg := fg) x f.scope)
      else 0)

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

/-- Preferred honest name for the list-based exact query semantics. -/
noncomputable def semanticWeightOfConstraintsList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  weightOfConstraintsList (fg := fg) fs constraints

/-- Preferred honest name for the factor-graph exact query semantics. -/
noncomputable def semanticWeightOfConstraints
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] : K :=
  weightOfConstraints (fg := fg) constraints

@[simp] theorem semanticWeightOfConstraintsList_eq_weightOfConstraintsList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] :
    semanticWeightOfConstraintsList (fg := fg) fs constraints =
      weightOfConstraintsList (fg := fg) fs constraints := rfl

@[simp] theorem semanticWeightOfConstraints_eq_weightOfConstraints
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] :
    semanticWeightOfConstraints (fg := fg) constraints =
      weightOfConstraints (fg := fg) constraints := rfl

/-- Fully operational exact query weight: add explicit indicator factors, add neutral
scope-covering unary factors, eliminate every variable, then evaluate the constant factor. -/
noncomputable def veQueryWeightList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K := by
  classical
  let φ := combineAll (fg := fg) (veFactorList (fg := fg) fs constraints)
  let ψ := sumOutAll (fg := fg) φ (Finset.univ : Finset V).toList
  exact Factor.evalConst (φ := ψ) (sumOutAll_scope_univ (f := φ))

@[simp] theorem veQueryWeightList_eq_weightOfConstraintsList
    (fg : FactorGraph V K)
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] :
    veQueryWeightList fg fs constraints =
      weightOfConstraintsList (fg := fg) fs constraints := by
  classical
  letI : Fintype fg.FullConfig := by
    dsimp [FactorGraph.FullConfig]
    infer_instance
  let φ := combineAll (fg := fg) (veFactorList (fg := fg) fs constraints)
  let ψ := sumOutAll (fg := fg) φ (Finset.univ : Finset V).toList
  calc
    veQueryWeightList fg fs constraints
        = Factor.evalConst (φ := ψ) (sumOutAll_scope_univ (f := φ)) := by
            simp [veQueryWeightList, φ, ψ]
    _ = Factor.totalWeight (φ := ψ) := by
          symm
          exact Factor.totalWeight_eq_evalConst_of_scope_empty (φ := ψ)
            (sumOutAll_scope_univ (f := φ))
    _ = Factor.totalWeight (φ := φ) := by
          simp [φ, ψ, totalWeight_sumOutAll]
    _ = Factor.fullConfigWeightSum (φ := φ) := by
          exact Factor.totalWeight_eq_fullConfigSum_of_scope_univ (φ := φ)
            (veFactorList_scope_univ (fs := fs) (constraints := constraints))
    _ = ∑ x : fg.FullConfig,
          if ∀ c ∈ constraints, x c.1 = c.2 then
            (combineAll (fg := fg) fs).potential
              (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
          else 0 := by
            unfold Factor.fullConfigWeightSum
            apply Fintype.sum_congr
            intro x
            by_cases hs : ∀ c ∈ constraints, x c.1 = c.2
            · rw [combineAll_potential_fullAssign_listProd
                  (fs := veFactorList (fg := fg) fs constraints) x]
              simp [veFactorList, List.map_append, List.prod_append,
                constraintFactors_product_fullAssign, coveringFactors_product_fullAssign,
                combineAll_potential_fullAssign_listProd]
            · rw [combineAll_potential_fullAssign_listProd
                  (fs := veFactorList (fg := fg) fs constraints) x]
              simp [veFactorList, List.map_append, List.prod_append,
                constraintFactors_product_fullAssign, coveringFactors_product_fullAssign,
                hs]
    _ = weightOfConstraintsList (fg := fg) fs constraints := by
          rfl

/-- Graph-level operational exact query weight. -/
noncomputable def veQueryWeight
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] : K :=
  veQueryWeightList fg (factorsOfGraph (fg := fg)) constraints

@[simp] theorem veQueryWeight_eq_weightOfConstraints
    (fg : FactorGraph V K)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] :
    veQueryWeight fg constraints = weightOfConstraints (fg := fg) constraints := by
  unfold veQueryWeight weightOfConstraints
  exact veQueryWeightList_eq_weightOfConstraintsList fg (factorsOfGraph (fg := fg)) constraints

/-! ## BN queries via VE (prop/link) -/

namespace BayesianNetwork

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.DiscreteCPT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)

/-- Exact probability of an event `v = val`.

This is kept under a historical VE-facing name for compatibility, but the
current implementation routes through the explicit exact VE elimination
surface. -/
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
    let num := veQueryWeight fg [⟨v, val⟩]
    let den := veQueryWeight fg []
    exact if den = 0 then 0 else num / den

/-- Exact conditional probability `P(B = valB | A = valA)`.

This is kept under a historical VE-facing name for compatibility, but the
current implementation routes through the explicit exact VE elimination
surface. -/
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
    let num := veQueryWeight fg [⟨a, valA⟩, ⟨b, valB⟩]
    let den := veQueryWeight fg [⟨a, valA⟩]
    exact if den = 0 then 0 else num / den

/-- Exact conditional probability `P(B = valB | constraints)`.

This is kept under a historical VE-facing name for compatibility, but the
current implementation routes through the explicit exact VE elimination
surface. -/
noncomputable def linkProbVECond (cpt : bn.DiscreteCPT)
    (constraints : List (Σ v : V, bn.stateSpace v)) (b : Σ v : V, bn.stateSpace v)
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
    let num := veQueryWeight fg (constraints ++ [b])
    let den := veQueryWeight fg constraints
    exact if den = 0 then 0 else num / den

/-- Preferred honest name for the exact semantic probability query surface. -/
noncomputable def propProbSemantic (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : ENNReal :=
  propProbVE (bn := bn) cpt v val

/-- Preferred honest name for the exact semantic binary conditional query surface. -/
noncomputable def linkProbSemantic (cpt : bn.DiscreteCPT)
    (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : ENNReal :=
  linkProbVE (bn := bn) cpt a b valA valB

/-- Preferred honest name for the exact semantic constrained conditional query surface. -/
noncomputable def linkProbSemanticCond (cpt : bn.DiscreteCPT)
    (constraints : List (Σ v : V, bn.stateSpace v)) (b : Σ v : V, bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : ENNReal :=
  linkProbVECond (bn := bn) cpt constraints b

@[simp] theorem propProbSemantic_eq_propProbVE
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    propProbSemantic (bn := bn) cpt v val = propProbVE (bn := bn) cpt v val := rfl

@[simp] theorem linkProbSemantic_eq_linkProbVE
    (cpt : bn.DiscreteCPT)
    (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    linkProbSemantic (bn := bn) cpt a b valA valB =
      linkProbVE (bn := bn) cpt a b valA valB := rfl

@[simp] theorem linkProbSemanticCond_eq_linkProbVECond
    (cpt : bn.DiscreteCPT)
    (constraints : List (Σ v : V, bn.stateSpace v)) (b : Σ v : V, bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    linkProbSemanticCond (bn := bn) cpt constraints b =
      linkProbVECond (bn := bn) cpt constraints b := rfl

end BayesianNetwork

end VariableElimination

end Mettapedia.ProbabilityTheory.BayesianNetworks
