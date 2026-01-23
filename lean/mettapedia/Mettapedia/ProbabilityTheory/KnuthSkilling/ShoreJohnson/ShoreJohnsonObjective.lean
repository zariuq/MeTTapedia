import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonInference
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonConstraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonTheorem

/-!
# Shore–Johnson: objective-function layer (discrete skeleton)

Shore–Johnson (1980) is fundamentally about an **inference operator**
`p ∘ I = q` realized by minimizing some functional `H(q,p)` over a constraint set.

Our project currently has:
- an operator-level axiom interface (`ShoreJohnsonInference.lean`), and
- an objective-level functional-equation analysis yielding `log` / KL rigidity
  (`ShoreJohnsonTheorem.lean`, `ShoreJohnsonKL.lean`).

This file provides a small amount of glue for talking about objective-based inference in the
finite/discrete setting, without yet committing to Shore–Johnson’s full expected-value constraint
language.

No Shore–Johnson uniqueness theorem is proved here; this is infrastructure.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective

open Classical

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonProof
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints

/-! ## Objective-based inference (relation form) -/

/-- An objective functional on finite distributions. -/
structure ObjectiveFunctional where
  D : ∀ {n : ℕ}, ProbDist n → ProbDist n → ℝ
  DProd : ∀ {n m : ℕ}, ProbDistProd n m → ProbDistProd n m → ℝ

/-- `q` is a minimizer of the objective `D(·,p)` over a constraint set `C`. -/
def IsMinimizer (F : ObjectiveFunctional) {n : ℕ} (p : ProbDist n)
    (C : ShoreJohnsonInference.ConstraintSet n)
    (q : ProbDist n) : Prop :=
  q ∈ C ∧ ∀ q' ∈ C, F.D q p ≤ F.D q' p

/-- `q` is a minimizer of the product objective `DProd(·,p)` over a product constraint set. -/
def IsMinimizerProd (F : ObjectiveFunctional) {n m : ℕ} (p : ProbDistProd n m)
    (C : ShoreJohnsonInference.ConstraintSetProd n m) (q : ProbDistProd n m) : Prop :=
  q ∈ C ∧ ∀ q' ∈ C, F.DProd q p ≤ F.DProd q' p

/-! ## Objective realization and equivalence -/

/-- An inference method is realized by an objective functional. -/
structure Realizes (I : ShoreJohnsonInference.InferenceMethod) (F : ObjectiveFunctional) : Prop where
  infer_iff_minimizer :
    ∀ {n : ℕ} (p : ProbDist n) (C : ShoreJohnsonInference.ConstraintSet n) (q : ProbDist n),
      I.Infer p C q ↔ IsMinimizer F p C q
  inferProd_iff_minimizer :
    ∀ {n m : ℕ} (p : ProbDistProd n m) (C : ShoreJohnsonInference.ConstraintSetProd n m)
      (q : ProbDistProd n m),
      I.InferProd p C q ↔ IsMinimizerProd F p C q

/-- An inference method is realized by an objective functional, *restricted to expected-value
constraint sets*.

This matches the scope of Shore–Johnson's 1980 theorem, which is stated for constraints given as
expected values (affine equalities). -/
structure RealizesEV (I : ShoreJohnsonInference.InferenceMethod) (F : ObjectiveFunctional) : Prop where
  infer_iff_minimizer_ev :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n),
      I.Infer p (toConstraintSet cs) q ↔ IsMinimizer F p (toConstraintSet cs) q

theorem Realizes.toRealizesEV
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (h : Realizes I F) : RealizesEV I F := by
  refine ⟨?_⟩
  intro n p cs q
  simpa using (h.infer_iff_minimizer p (toConstraintSet cs) q)

/-- Objective-level equivalence: identical minimizers for every prior and constraint set. -/
def ObjEquiv (F G : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (p : ProbDist n) (C : ShoreJohnsonInference.ConstraintSet n),
    {q | IsMinimizer F p C q} = {q | IsMinimizer G p C q}

/-- Objective equivalence restricted to expected-value constraint sets. -/
def ObjEquivEV (F G : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n),
    {q | IsMinimizer F p (toConstraintSet cs) q} = {q | IsMinimizer G p (toConstraintSet cs) q}

theorem objEquivEV_isMinimizer_iff
    {F G : ObjectiveFunctional} (hEq : ObjEquivEV F G)
    {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n) :
    IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer G p (toConstraintSet cs) q := by
  have h := congrArg (fun s => q ∈ s) (hEq (n := n) p cs)
  simpa using h

theorem objEquiv_refl (F : ObjectiveFunctional) : ObjEquiv F F := by
  intro n p C
  rfl

theorem objEquivEV_refl (F : ObjectiveFunctional) : ObjEquivEV F F := by
  intro n p cs
  rfl

theorem objEquiv_symm {F G : ObjectiveFunctional} (h : ObjEquiv F G) : ObjEquiv G F := by
  intro n p C
  simpa using (h (n := n) p C).symm

theorem objEquivEV_symm {F G : ObjectiveFunctional} (h : ObjEquivEV F G) : ObjEquivEV G F := by
  intro n p cs
  simpa using (h (n := n) p cs).symm

theorem objEquiv_trans {F G H : ObjectiveFunctional} (hFG : ObjEquiv F G) (hGH : ObjEquiv G H) :
    ObjEquiv F H := by
  intro n p C
  exact (hFG (n := n) p C).trans (hGH (n := n) p C)

theorem objEquivEV_trans {F G H : ObjectiveFunctional} (hFG : ObjEquivEV F G) (hGH : ObjEquivEV G H) :
    ObjEquivEV F H := by
  intro n p cs
  exact (hFG (n := n) p cs).trans (hGH (n := n) p cs)

theorem objEquiv_of_realizes
    {I : ShoreJohnsonInference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : Realizes I F) (hG : Realizes I G) :
    ObjEquiv F G := by
  intro n p C
  ext q
  constructor
  · intro hq
    exact (hG.infer_iff_minimizer p C q).1 ((hF.infer_iff_minimizer p C q).2 hq)
  · intro hq
    exact (hF.infer_iff_minimizer p C q).1 ((hG.infer_iff_minimizer p C q).2 hq)

theorem objEquivEV_of_realizesEV
    {I : ShoreJohnsonInference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : RealizesEV I F) (hG : RealizesEV I G) :
    ObjEquivEV F G := by
  intro n p cs
  ext q
  constructor
  · intro hq
    exact (hG.infer_iff_minimizer_ev p cs q).1 ((hF.infer_iff_minimizer_ev p cs q).2 hq)
  · intro hq
    exact (hF.infer_iff_minimizer_ev p cs q).1 ((hG.infer_iff_minimizer_ev p cs q).2 hq)

theorem realizesEV_of_objEquivEV
    {I : ShoreJohnsonInference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : RealizesEV I F) (hEq : ObjEquivEV F G) :
    RealizesEV I G := by
  refine ⟨?_⟩
  intro n p cs q
  have hMin : IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer G p (toConstraintSet cs) q :=
    objEquivEV_isMinimizer_iff (hEq := hEq) (p := p) (cs := cs) (q := q)
  exact (hF.infer_iff_minimizer_ev p cs q).trans hMin

theorem unique_minimizer_of_realizes
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : ShoreJohnsonInference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
    ∀ {n : ℕ} (p : ProbDist n) (C : ShoreJohnsonInference.ConstraintSet n),
      ∃! q : ProbDist n, IsMinimizer F p C q := by
  intro n p C
  rcases hSJ.unique p C with ⟨q, hq, huniq⟩
  refine ⟨q, (hF.infer_iff_minimizer p C q).1 hq, ?_⟩
  intro q' hq'
  apply huniq
  exact (hF.infer_iff_minimizer p C q').2 hq'

/-! ## Objective-level consequences of SJ2/SJ3/SJ4 -/

theorem isMinimizer_permute_of_realizes
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : ShoreJohnsonInference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n)
    (C : ShoreJohnsonInference.ConstraintSet n) (q : ProbDist n),
    IsMinimizer F p C q →
        IsMinimizer F (ShoreJohnsonInference.ProbDist.permute σ p)
          (ShoreJohnsonInference.ConstraintSet.permute σ C)
          (ShoreJohnsonInference.ProbDist.permute σ q) := by
  intro n σ p C q hmin
  have hInf : I.Infer p C q := (hF.infer_iff_minimizer p C q).2 hmin
  have hInf' := hSJ.perm_invariant σ p C q hInf
  exact (hF.infer_iff_minimizer _ _ _).1 hInf'

theorem eq_twoBlock_of_isMinimizer_twoBlock
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : ShoreJohnsonInference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
  ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : ShoreJohnsonInference.ConstraintSet n) (C₂ : ShoreJohnsonInference.ConstraintSet m)
    (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
    IsMinimizer F p₁ C₁ q₁ →
    IsMinimizer F p₂ C₂ q₂ →
      IsMinimizer F (ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (ShoreJohnsonInference.ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q →
      q = ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂ := by
  intro n m w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q hq₁ hq₂ hq
  have hInf₁ : I.Infer p₁ C₁ q₁ := (hF.infer_iff_minimizer p₁ C₁ q₁).2 hq₁
  have hInf₂ : I.Infer p₂ C₂ q₂ := (hF.infer_iff_minimizer p₂ C₂ q₂).2 hq₂
  have hInf :
      I.Infer (ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (ShoreJohnsonInference.ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q :=
    (hF.infer_iff_minimizer _ _ _).2 hq
  exact hSJ.subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q hInf₁ hInf₂ hInf

theorem eq_twoBlock_of_isMinimizer_twoBlock_ev
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : ShoreJohnsonInference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p₁ : ProbDist n) (p₂ : ProbDist m)
      (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
      IsMinimizer F p₁ (toConstraintSet cs₁) q₁ →
      IsMinimizer F p₂ (toConstraintSet cs₂) q₂ →
      IsMinimizer F (ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)) q →
      q = ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q₁ q₂ := by
  intro n m w hw0 hw1 p₁ p₂ cs₁ cs₂ q₁ q₂ q hq₁ hq₂ hq
  have heq :
      toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) =
        ShoreJohnsonInference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂) :=
    twoBlockConstraints_equiv_set (n := n) (m := m) w hw0 hw1 cs₁ cs₂
  have hq' :
      IsMinimizer F
        (ShoreJohnsonInference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (ShoreJohnsonInference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂)) q := by
    rcases hq with ⟨hq_mem, hq_le⟩
    refine ⟨?_, ?_⟩
    · simpa [heq] using hq_mem
    · intro q' hq'
      have hq'' : q' ∈ toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) := by
        simpa [heq] using hq'
      exact hq_le q' hq''
  exact eq_twoBlock_of_isMinimizer_twoBlock (hSJ := hSJ) (hF := hF) w (le_of_lt hw0) (le_of_lt hw1)
    p₁ p₂ (toConstraintSet cs₁) (toConstraintSet cs₂) q₁ q₂ q hq₁ hq₂ hq'

theorem eq_prod_of_isMinimizer_product
    {I : ShoreJohnsonInference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : ShoreJohnsonInference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
    ∀ {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : ShoreJohnsonInference.ConstraintSet n) (C₂ : ShoreJohnsonInference.ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDistProd n m),
      IsMinimizer F p₁ C₁ q₁ →
      IsMinimizer F p₂ C₂ q₂ →
      IsMinimizerProd F (p₁ ⊗ p₂) (ShoreJohnsonInference.ConstraintSetProd.product C₁ C₂) q →
      q = (q₁ ⊗ q₂) := by
  intro n m p₁ p₂ C₁ C₂ q₁ q₂ q hq₁ hq₂ hq
  have hInf₁ : I.Infer p₁ C₁ q₁ := (hF.infer_iff_minimizer p₁ C₁ q₁).2 hq₁
  have hInf₂ : I.Infer p₂ C₂ q₂ := (hF.infer_iff_minimizer p₂ C₂ q₂).2 hq₂
  have hInf :
      I.InferProd (p₁ ⊗ p₂) (ShoreJohnsonInference.ConstraintSetProd.product C₁ C₂) q :=
    (hF.inferProd_iff_minimizer _ _ _).2 hq
  exact hSJ.system_independent p₁ p₂ C₁ C₂ q₁ q₂ q hInf₁ hInf₂ hInf

/-! ## Atom-sum objectives -/

/-- Build an objective functional from an atom divergence `d` by summing over indices. -/
noncomputable def ofAtom (d : ℝ → ℝ → ℝ) : ObjectiveFunctional where
  D := fun {n} q p => ∑ i : Fin n, d (q.p i) (p.p i)
  DProd := fun {n m} q p => ∑ ij : Fin n × Fin m, d (q.p ij) (p.p ij)

/-! ## Objective equivalences -/

theorem objEquiv_of_pointwise_eq
    {F : ObjectiveFunctional} (d : ℝ → ℝ → ℝ)
    (hD : ∀ {n : ℕ} (q p : ProbDist n),
      F.D q p = ∑ i : Fin n, d (q.p i) (p.p i)) :
    ObjEquiv F (ofAtom d) := by
  intro n p C
  ext q
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    simpa [ofAtom, hD] using hle
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    simpa [ofAtom, hD] using hle

theorem isMinimizer_const_mul_ofAtom_iff {n : ℕ} (c : ℝ) (hc : 0 < c)
    (d : ℝ → ℝ → ℝ)
    (p : ProbDist n) (C : ShoreJohnsonInference.ConstraintSet n) (q : ProbDist n) :
    IsMinimizer (ofAtom d) p C q ↔ IsMinimizer (ofAtom (fun w u => c * d w u)) p C q := by
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    -- Scale both sides by `c` (positive) and pull `c` out of the sums.
    have hle' : c * (∑ i : Fin n, d (q.p i) (p.p i)) ≤ c * (∑ i : Fin n, d (q'.p i) (p.p i)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hc)
    -- Rewrite each objective value as `c * sum`.
    simpa [ofAtom, Finset.mul_sum, mul_assoc] using hle'
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    -- Divide by `c` by scaling with `c⁻¹` (still positive).
    have hc' : 0 < c⁻¹ := inv_pos.2 hc
    have hle' :
        c⁻¹ * (∑ i : Fin n, (c * d (q.p i) (p.p i))) ≤
          c⁻¹ * (∑ i : Fin n, (c * d (q'.p i) (p.p i))) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hc')
    -- Simplify `c⁻¹ * c = 1`.
    have : (∑ i : Fin n, d (q.p i) (p.p i)) ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := by
      simpa [Finset.mul_sum, inv_mul_cancel_left₀ hc.ne', mul_assoc] using hle'
    simpa [ofAtom] using this

theorem objEquiv_const_mul_ofAtom (c : ℝ) (hc : 0 < c) (d : ℝ → ℝ → ℝ) :
    ObjEquiv (ofAtom d) (ofAtom (fun w u => c * d w u)) := by
  intro n p C
  ext q
  exact isMinimizer_const_mul_ofAtom_iff (n := n) c hc d p C q

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective
