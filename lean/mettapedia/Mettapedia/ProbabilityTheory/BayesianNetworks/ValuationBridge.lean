import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationAlgebra

/-!
# Factor → Valuation Bridge (VE Correctness Reuse)

This module connects concrete factor-graph factors to the valuation-algebra layer.
The goal is to **reuse the VE correctness spine** (`combineAll_eliminateVars`) for
the concrete BN/FG engine by transporting factors into valuations.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace ValuationBridge

open VariableElimination

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

/-! ## Factor → Valuation -/

noncomputable def fullAssign
    (x : FullConfig V (fun v => fg.stateSpace v)) (S : Finset V) :
    FactorGraph.Assign (fg := fg) S := fun v _ => x v

/-- Interpret a factor as a valuation on full configurations. -/
noncomputable def toValuation (φ : Factor fg) :
    Valuation V (fun v => fg.stateSpace v) K :=
  { scope := φ.scope
    val := fun x => φ.potential (fullAssign (fg := fg) x φ.scope) }

/-- Map a factor list into valuation form. -/
noncomputable def toValuations (fs : List (Factor fg)) :
    List (Valuation V (fun v => fg.stateSpace v) K) :=
  fs.map (toValuation (fg := fg))

omit [DecidableEq V] in
lemma toValuation_respects (φ : Factor fg) :
    RespectsScope (toValuation (fg := fg) φ) := by
  intro x y hxy
  have hfun : fullAssign (fg := fg) x φ.scope = fullAssign (fg := fg) y φ.scope := by
    funext v hv
    exact hxy v hv
  simp [toValuation, hfun]

lemma extend_eq_update (φ : Factor fg) (v : V) (hv : v ∈ φ.scope)
    (x : FullConfig V (fun v => fg.stateSpace v)) (val : fg.stateSpace v) :
    Factor.extend (φ := φ) v hv (fullAssign (fg := fg) x (φ.scope.erase v)) val =
      (fun u (_ : u ∈ φ.scope) =>
        update (V := V) (β := fun v => fg.stateSpace v) x v val u) := by
  funext u hu
  classical
  by_cases h : u = v
  · subst h
    simp [Factor.extend, update]
  · have : u ∈ φ.scope.erase v := by
      exact Finset.mem_erase.mpr ⟨h, hu⟩
    simp [Factor.extend, update, fullAssign, h]

omit [DecidableEq V] in
lemma toValuation_oneFactor [One K] :
    toValuation (fg := fg) (VariableElimination.oneFactor (fg := fg)) =
      oneValuation V (fun v => fg.stateSpace v) K := by
  apply Valuation.ext
  · rfl
  · intro x
    simp [toValuation, VariableElimination.oneFactor, oneValuation]

lemma toValuation_mul (φ ψ : Factor fg) [Mul K] :
    toValuation (fg := fg) (Factor.mul (fg := fg) φ ψ) =
      combine (φ := toValuation (fg := fg) φ) (ψ := toValuation (fg := fg) ψ) := by
  apply Valuation.ext
  · ext v
    simp [toValuation, Factor.mul, combine, Finset.mem_union]
  · intro x
    rfl

lemma toValuation_sumOut (φ : Factor fg) (v : V)
    [Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    toValuation (fg := fg) (Factor.sumOut (fg := fg) (φ := φ) v) =
      sumOut (φ := toValuation (fg := fg) φ) v := by
  classical
  by_cases hv : v ∈ φ.scope
  · apply Valuation.ext
    · simp [toValuation, Factor.sumOut, sumOut, hv]
    · intro x
      have hsumOut_def :
          Factor.sumOut (fg := fg) (φ := φ) v =
            { scope := φ.scope.erase v
              potential := fun x =>
                ∑ val : fg.stateSpace v, φ.potential (Factor.extend (φ := φ) v hv x val) } := by
        simp [Factor.sumOut, hv]
      have hsumOut_val :
          (toValuation (fg := fg) (Factor.sumOut (fg := fg) (φ := φ) v)).val x =
            ∑ val : fg.stateSpace v,
              φ.potential (Factor.extend (φ := φ) v hv (fullAssign (fg := fg) x (φ.scope.erase v)) val) := by
        rw [hsumOut_def]
        simp [toValuation]
      have hsum :
          (∑ val : fg.stateSpace v,
              φ.potential (Factor.extend (φ := φ) v hv (fullAssign (fg := fg) x (φ.scope.erase v)) val)) =
            ∑ val : fg.stateSpace v,
              φ.potential (fullAssign (fg := fg)
                (update (V := V) (β := fun v => fg.stateSpace v) x v val) φ.scope) := by
        refine Finset.sum_congr rfl ?_
        intro val _
        have := congrArg (fun f => φ.potential f)
          (extend_eq_update (φ := φ) (v := v) (hv := hv) (x := x) (val := val))
        simpa [fullAssign] using this
      have hsumOut_right :
          (sumOut (φ := toValuation (fg := fg) φ) v).val x =
            ∑ val : fg.stateSpace v,
              φ.potential (fullAssign (fg := fg)
                (update (V := V) (β := fun v => fg.stateSpace v) x v val) φ.scope) := by
        simp [toValuation, sumOut, hv]
      calc
        (toValuation (fg := fg) (Factor.sumOut (fg := fg) (φ := φ) v)).val x =
            ∑ val : fg.stateSpace v,
              φ.potential (Factor.extend (φ := φ) v hv (fullAssign (fg := fg) x (φ.scope.erase v)) val) := by
                exact hsumOut_val
        _ = ∑ val : fg.stateSpace v,
              φ.potential (fullAssign (fg := fg)
                (update (V := V) (β := fun v => fg.stateSpace v) x v val) φ.scope) := by
                exact hsum
        _ = (sumOut (φ := toValuation (fg := fg) φ) v).val x := by
                symm
                exact hsumOut_right
  · -- v not in scope: both sides are identity
    have hsumOut_def : Factor.sumOut (fg := fg) (φ := φ) v = φ := by
      simp [Factor.sumOut, hv]
    rw [hsumOut_def]
    simp [toValuation, sumOut, hv]

lemma toValuation_combineAll (fs : List (Factor fg)) [One K] [Mul K] :
    toValuation (fg := fg) (VariableElimination.combineAll (fg := fg) fs) =
      combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
        (toValuations (fg := fg) fs) := by
  classical
  induction fs with
  | nil =>
      simp [VariableElimination.combineAll, toValuations, toValuation_oneFactor, combineAll]
  | cons f fs ih =>
      calc
        toValuation (fg := fg) (VariableElimination.combineAll (fg := fg) (f :: fs)) =
            combine (φ := toValuation (fg := fg) f)
              (ψ := toValuation (fg := fg) (VariableElimination.combineAll (fg := fg) fs)) := by
                simp [VariableElimination.combineAll, toValuation_mul]
        _ = combine (φ := toValuation (fg := fg) f)
              (ψ := combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
                (toValuations (fg := fg) fs)) := by
                simp [ih]
        _ = combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
              (toValuations (fg := fg) (f :: fs)) := by
                simp [combineAll, toValuations]

lemma toValuation_sumOutAll (f : Factor fg) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K] :
    toValuation (fg := fg) (VariableElimination.sumOutAll (fg := fg) f order) =
      sumOutAll (φ := toValuation (fg := fg) f) order := by
  classical
  induction order generalizing f with
  | nil =>
      simp [VariableElimination.sumOutAll, sumOutAll]
  | cons v vs ih =>
      have h := ih (Factor.sumOut (fg := fg) (φ := f) v)
      simpa [VariableElimination.sumOutAll, sumOutAll, toValuation_sumOut] using h

/-! ## VE correctness reuse (valuation layer) -/

theorem eliminateVars_correct_via_valuation
    (fs : List (Factor fg)) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :
    combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
        (eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := K)
          (toValuations (fg := fg) fs) order) =
      sumOutAll (φ := combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
        (toValuations (fg := fg) fs)) order := by
  classical
  have hres : RespectsAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
      (toValuations (fg := fg) fs) := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
    exact toValuation_respects (fg := fg) g
  exact
    combineAll_eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := K)
      (fs := toValuations (fg := fg) fs) (order := order) hres

/-- Factor-graph semantics → valuation VE:
combine+sumOut in the concrete engine matches valuation elimination. -/
theorem sumOutAll_combineAll_via_valuation
    (fs : List (Factor fg)) (order : List V)
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :
    toValuation (fg := fg)
        (VariableElimination.sumOutAll (fg := fg)
          (VariableElimination.combineAll (fg := fg) fs) order) =
      combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
        (eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := K)
          (toValuations (fg := fg) fs) order) := by
  classical
  have h₁ :
      toValuation (fg := fg)
          (VariableElimination.sumOutAll (fg := fg)
            (VariableElimination.combineAll (fg := fg) fs) order) =
        sumOutAll (φ := toValuation (fg := fg)
          (VariableElimination.combineAll (fg := fg) fs)) order := by
    simpa using
      (toValuation_sumOutAll (fg := fg)
        (f := VariableElimination.combineAll (fg := fg) fs) order)
  have h₂ :
      toValuation (fg := fg) (VariableElimination.combineAll (fg := fg) fs) =
        combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
          (toValuations (fg := fg) fs) := by
    simpa using (toValuation_combineAll (fg := fg) (fs := fs))
  calc
    toValuation (fg := fg)
        (VariableElimination.sumOutAll (fg := fg)
          (VariableElimination.combineAll (fg := fg) fs) order)
        = sumOutAll (φ := toValuation (fg := fg)
            (VariableElimination.combineAll (fg := fg) fs)) order := h₁
    _ = sumOutAll (φ := combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
            (toValuations (fg := fg) fs)) order := by
          simp [h₂]
    _ = combineAll (V := V) (β := fun v => fg.stateSpace v) (K := K)
          (eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := K)
            (toValuations (fg := fg) fs) order) := by
          simpa using
            (eliminateVars_correct_via_valuation (fg := fg) (fs := fs) (order := order)).symm

end ValuationBridge

end Mettapedia.ProbabilityTheory.BayesianNetworks
