import Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalConstraintBounds

/-!
# Rational certificates for conditional probability bounds

A nonnegative combination of the scaled model's inequalities certifies
an endpoint bound. A feasible rational model can witness attainment.
Certificate generation is independent of validation.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalCertificates

open Mettapedia.Logic.Arithmetic.FourierMotzkin
open FiniteConditionalConstraints ConditionalConstraintBounds

private def add {n : Nat} (x y : LinTerm n) : LinTerm n := x.sub (y.scale (-1))

private theorem add_eval {n : Nat} (x y : LinTerm n) (env : Fin n → ℝ) :
    (add x y).eval env = x.eval env + y.eval env := by
  simp [add, eval_sub, eval_scale, sub_eq_add_neg]

private def combine {n : Nat} (rows : List (Atom n)) (weights : List ℚ) : LinTerm n :=
  ((rows.zip weights).map (fun (row, weight) => row.term.scale weight)).foldr add (constant 0)

private theorem combine_nonpos {n : Nat} (rows : List (Atom n)) (weights : List ℚ)
    (positive : ∀ w ∈ weights, 0 ≤ w) (env : Fin n → ℝ) (satisfied : allSat rows env) :
    (combine rows weights).eval env ≤ 0 := by
  induction rows generalizing weights with
  | nil => simp [combine]
  | cons row rest ih =>
    cases weights with
    | nil => simp [combine]
    | cons w tail =>
      rw [allSat_cons] at satisfied
      have rowNonpos : row.term.eval env ≤ 0 := by
        cases rel : row.rel
        · simpa only [Atom.sat, rel, holds] using satisfied.1
        · exact (show row.term.eval env < 0 by
            simpa only [Atom.sat, rel, holds] using satisfied.1).le
      have scale : 0 ≤ (w : ℝ) := Rat.cast_nonneg.mpr (positive _ List.mem_cons_self)
      have smaller := ih tail (fun a h => positive a (List.mem_cons_of_mem _ h)) satisfied.2
      change (add (row.term.scale w) (combine rest tail)).eval env ≤ 0
      rw [add_eval, eval_scale]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos scale rowNonpos) smaller

def checkedCombination {n : Nat} (rows : List (Atom n)) (weights : List ℚ) (target : LinTerm n) : Bool :=
  (decide (weights.length = rows.length) && weights.all (fun w => decide (0 ≤ w))) &&
    decide (combine rows weights = target)

theorem checkedCombination_sound {n : Nat} (rows : List (Atom n)) (weights : List ℚ)
    (target : LinTerm n) (accepted : checkedCombination rows weights target = true)
    (env : Fin n → ℝ) (satisfied : allSat rows env) : target.eval env ≤ 0 := by
  simp only [checkedCombination, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  rw [← accepted.2]
  exact combine_nonpos rows weights accepted.1.2 env satisfied

private theorem dot_cast {n : Nat} (cs : Coeff n) (env : Fin n → ℚ) :
    ((cs.dot env : ℚ) : ℝ) = cs.dot (fun i => (env i : ℝ)) := by
  induction cs with
  | nil => simp [Coeff.dot]
  | cons head tail ih => simp [Coeff.dot, ih]

private theorem eval_cast {n : Nat} (term : LinTerm n) (env : Fin n → ℚ) :
    ((term.eval env : ℚ) : ℝ) = term.eval (fun i => (env i : ℝ)) := by
  simp [LinTerm.eval, dot_cast]

private def checkRow {n : Nat} (env : Fin n → ℚ) (row : Atom n) : Bool :=
  match row.rel with
  | .le => decide (row.term.eval env ≤ 0)
  | .lt => decide (row.term.eval env < 0)

def checkedModel {n : Nat} (rows : List (Atom n)) (env : Fin n → ℚ) : Bool :=
  rows.all (checkRow env)

theorem checkedModel_sound {n : Nat} (rows : List (Atom n)) (env : Fin n → ℚ)
    (accepted : checkedModel rows env = true) : allSat rows (fun i => (env i : ℝ)) := by
  intro row member
  have test := List.all_eq_true.mp accepted row member
  unfold checkRow at test
  rw [Atom.sat, ← eval_cast]
  cases h : row.rel <;> simp_all [holds]

structure Endpoint where
  value : ℚ
  weights : List ℚ

def lowerTarget {n : Nat} (bound : ℚ) : LinTerm (n + 1) :=
  (constant bound).sub (varTerm (Fin.last n))

def upperTarget {n : Nat} (bound : ℚ) : LinTerm (n + 1) :=
  (varTerm (Fin.last n)).sub (constant bound)

def checkBounds {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : Endpoint) : Bool :=
  let rows := scaledAtoms base event condition
  checkedCombination rows lower.weights (lowerTarget lower.value) &&
    checkedCombination rows upper.weights (upperTarget upper.value)

theorem checkBounds_sound {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : Endpoint) (accepted : checkBounds base event condition lower upper = true) :
    queryValues base event condition ⊆ Set.Icc (lower.value : ℝ) (upper.value : ℝ) := by
  intro value possible
  obtain ⟨env, model, same⟩ :=
    (projectToOne_sat n _ value).mp ((projected_values base event condition value).mpr possible)
  simp only [checkBounds, Bool.and_eq_true] at accepted
  obtain ⟨lo, hi⟩ := accepted
  have first := checkedCombination_sound _ _ _ lo env model
  have last := checkedCombination_sound _ _ _ hi env model
  simpa only [Set.mem_Icc, lowerTarget, upperTarget, eval_sub, variable_eval,
    constant_eval, same, sub_nonpos] using And.intro first last

def witnessEnv {n : Nat} (value : ℚ) (weight : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.lastCases value weight

theorem witness_attains {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (value : ℚ) (weight : Fin n → ℚ)
    (accepted : checkedModel (scaledAtoms base event condition) (witnessEnv value weight) = true) :
    (value : ℝ) ∈ queryValues base event condition := by
  apply (projected_values base event condition _).mp
  apply (projectToOne_sat n _ _).mpr
  exact ⟨fun i => (witnessEnv value weight i : ℝ), checkedModel_sound _ _ accepted,
    by simp [witnessEnv]⟩

def checkSharp {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : Endpoint) (lowerModel upperModel : Fin n → ℚ) : Bool :=
  let rows := scaledAtoms base event condition
  (checkBounds base event condition lower upper &&
    checkedModel rows (witnessEnv lower.value lowerModel)) &&
    checkedModel rows (witnessEnv upper.value upperModel)

theorem checkSharp_exact {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : Endpoint) (lowerModel upperModel : Fin n → ℚ)
    (accepted : checkSharp base event condition lower upper lowerModel upperModel = true) :
    queryValues base event condition = Set.Icc (lower.value : ℝ) (upper.value : ℝ) := by
  simp only [checkSharp, Bool.and_eq_true] at accepted
  obtain ⟨⟨boundsOk, lowerOk⟩, upperOk⟩ := accepted
  apply bounds_exact_range
  exact queryBoundsRat_eq_of_witnesses base event condition _ _
    (witness_attains base event condition _ _ lowerOk) (witness_attains base event condition _ _ upperOk)
    (checkBounds_sound base event condition _ _ boundsOk)

/-- A positive constant derived from nonpositive rows refutes the model. -/
def checkImpossible {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (weights : List ℚ) : Bool :=
  checkedCombination (scaledAtoms base event condition) weights (constant 1)

theorem checkImpossible_empty {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (weights : List ℚ) (accepted : checkImpossible base event condition weights = true) :
    queryValues base event condition = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro value possible
  obtain ⟨env, model, _⟩ :=
    (projectToOne_sat n _ value).mp ((projected_values base event condition value).mpr possible)
  have nonpositive := checkedCombination_sound _ _ _ accepted env model
  rw [constant_eval, Rat.cast_one] at nonpositive
  exact (not_le_of_gt zero_lt_one) nonpositive

def checkConsistent {n : Nat} (base : KnowledgeBase (Fin n)) (weight : Fin n → ℚ) : Bool :=
  checkedModel (scaledAtoms base (fun _ => false) (fun _ => true)) (witnessEnv 0 weight)

theorem checkConsistent_sound {n : Nat} (base : KnowledgeBase (Fin n)) (weight : Fin n → ℚ)
    (accepted : checkConsistent base weight = true) : Consistent base := by
  obtain ⟨model, valid, _, _⟩ := witness_attains base (fun _ => false) (fun _ => true) 0 weight accepted
  exact ⟨model, valid⟩

def checkInconsistent {n : Nat} (base : KnowledgeBase (Fin n)) (weights : List ℚ) : Bool :=
  checkImpossible base (fun _ => false) (fun _ => true) weights

theorem checkInconsistent_sound {n : Nat} (base : KnowledgeBase (Fin n)) (weights : List ℚ)
    (accepted : checkInconsistent base weights = true) : ¬ Consistent base := by
  rintro ⟨model, valid⟩
  have positive : 0 < FiniteEventMass.mass model.weight (fun _ => true) := by
    simp [FiniteEventMass.mass, model.total]
  have empty := checkImpossible_empty base (fun _ => false) (fun _ => true) _ accepted
  exact Set.eq_empty_iff_forall_notMem.mp empty _ ⟨model, valid, positive, rfl⟩

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalCertificates
