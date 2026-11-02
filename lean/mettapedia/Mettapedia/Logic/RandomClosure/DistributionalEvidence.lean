import Mettapedia.Logic.RandomClosure
import Mettapedia.Logic.WorldModel.DistributionalSpace
import Mettapedia.OSLF.Framework.WMCalculusSemantics

/-!
# Evidence-bearing closure responses and WM readings

Independent component composition, alternative-world mixture and union of
identified observations have different algebras. Commonality gives a
multiplicative reading of the existing WM calculus; probability is obtained
only after signed extraction and normalization. Local evidence mass must
survive until the shared causes are mixed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.RandomClosure.DistributionalEvidence
open Finset Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Logic.DistributionalSpace
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open scoped Classical NNReal

variable {B Ω O Id Θ H I X : Type}

/-- A finite collection of alternatives, retaining their unnormalized masses. -/
abbrev Bag (B : Type*) := List (ClosureOperator (Set B) × ℝ≥0)

noncomputable def row (xs : Bag B) (F : Finset (Set B)) : ℝ :=
  (xs.map fun x => if Closes x.1 F then (x.2 : ℝ) else 0).sum

def compose (xs ys : Bag B) : Bag B :=
  xs.flatMap fun x => ys.map fun y => (join x.1 y.1, x.2 * y.2)

@[simp] theorem row_nil (F : Finset (Set B)) : row ([] : Bag B) F = 0 := rfl
@[simp] theorem row_cons (x : ClosureOperator (Set B) × ℝ≥0) (xs : Bag B) (F : Finset (Set B)) :
    row (x :: xs) F = (if Closes x.1 F then (x.2 : ℝ) else 0) + row xs F := rfl

theorem row_append (xs ys : Bag B) (F : Finset (Set B)) :
    row (xs ++ ys) F = row xs F + row ys F := by simp [row]

theorem row_join_scale (x : ClosureOperator (Set B) × ℝ≥0) (ys : Bag B)
    (F : Finset (Set B)) :
    row (ys.map fun y => (join x.1 y.1, x.2 * y.2)) F =
      (if Closes x.1 F then (x.2 : ℝ) else 0) * row ys F := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, row_cons, ih, closes_join, NNReal.coe_mul]
    by_cases hx : Closes x.1 F <;> by_cases hy : Closes y.1 F <;> simp [hx, hy]; ring

theorem row_compose (xs ys : Bag B) (F : Finset (Set B)) :
    row (compose xs ys) F = row xs F * row ys F := by
  induction xs with
  | nil => simp [compose]
  | cons x xs ih =>
    change row ((ys.map fun y => (join x.1 y.1, x.2 * y.2)) ++ compose xs ys) F = _
    rw [row_append, row_join_scale, ih, row_cons]
    ring

def unitBag : Bag B := [(ClosureOperator.id (Set B), 1)]
@[simp] theorem row_unit (F : Finset (Set B)) : row (unitBag : Bag B) F = 1 := by
  simp [unitBag, Closes, ClosureOperator.id]

/-- The historic evidence unit denotes multiplicative one in this reading.
Revision here means fresh independent choices, not ledger union. -/
noncomputable def reading (world : String → Bag B) (query : String → Finset (Set B)) :
    WMReading (Bag B) (Finset (Set B)) ℝ where
  revise := compose
  extract := row
  combine := (· * ·)
  zero := 1
  world := world
  query := query

theorem reading_laws (world : String → Bag B) (query : String → Finset (Set B)) :
    (reading world query).CoreLaws where
  extract_revise := row_compose
  combine_comm := mul_comm
  combine_assoc := mul_assoc
  combine_zero := mul_one

variable [Fintype B]

noncomputable def numerator (xs : Bag B) (seed : Set B) (q : B) : ℝ :=
  ∑ F ∈ (avoiding seed q).powerset, (-1 : ℝ)^F.card * row xs F
noncomputable def probability (xs : Bag B) (seed : Set B) (q : B) : Option ℝ :=
  if 0 < row xs ∅ then some (numerator xs seed q / row xs ∅) else none

omit [Fintype B] in
theorem row_nonnegative (xs : Bag B) (F : Finset (Set B)) : 0 ≤ row xs F := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    rw [row_cons]
    apply add_nonneg _ ih
    split_ifs
    · exact x.2.coe_nonneg
    · exact le_rfl

theorem probability_none_iff (xs : Bag B) (seed : Set B) (q : B) :
    probability xs seed q = none ↔ row xs ∅ = 0 := by
  simp only [probability, ite_eq_right_iff, reduceCtorEq, imp_false]
  have hn := row_nonnegative xs ∅
  exact ⟨fun h => le_antisymm (le_of_not_gt h) hn, fun h => by simp [h]⟩

theorem probability_of_agree (world : String → Bag B) (query : String → Finset (Set B))
    {xs ys : Bag B} (same : (reading world query).Agree .state xs ys) (seed : Set B) (q : B) :
    probability xs seed q = probability ys seed q := by
  have eqRow : ∀ F, row xs F = row ys F := same
  simp only [probability, numerator, eqRow]

/-- Existing contextual WM rewrites preserve the derived partial probability. -/
theorem contextual_probability (world : String → Bag B) (query : String → Finset (Set B))
    {s t : WMTerm .state} (steps : WMContextStepStar s t) (seed : Set B) (q : B) :
    probability ((reading world query).denote s) seed q =
      probability ((reading world query).denote t) seed q :=
  probability_of_agree world query ((reading_laws world query).agree_of_contextStepStar steps) seed q

omit [Fintype B] in
/-- Normalization eligibility is itself invariant under contextual rewriting. -/
theorem contextual_normalizer (world : String → Bag B) (query : String → Finset (Set B))
    {s t : WMTerm .state} (steps : WMContextStepStar s t) :
    row ((reading world query).denote s) ∅ = row ((reading world query).denote t) ∅ :=
  (reading_laws world query).agree_of_contextStepStar steps ∅

section Evidence
variable [Fintype Ω] [Fintype O]

/-- The source Space independently supplies the joint likelihood and prior. -/
noncomputable def spaceMass (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id) (w : Ω) : ℝ :=
  (m.prior θ).1 w * m.likelihood θ E w

omit [Fintype B] in
@[simp] theorem spaceMass_total (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id)
    (c : Ω → ClosureOperator (Set B)) : commonality (spaceMass m θ E) c ∅ = m.normalizer θ E := by
  rw [commonality_empty]
  rfl

/-- Signed commonality extraction and one normalization answer the Space query. -/
theorem space_probability (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id)
    (c : Ω → ClosureOperator (Set B)) (seed : Set B) (q : B) :
    m.probability? θ E (fun w => decide (q ∈ c w seed)) =
      if 0 < commonality (spaceMass m θ E) c ∅ then
        some (preparedExtract (spaceMass m θ E) c seed q /
          commonality (spaceMass m θ E) c ∅) else none := by
  rw [spaceMass_total, preparedExtract_correct, Model.probability?_formula]
  simp only [decide_eq_true_eq, spaceMass]

end Evidence

section OwnedObservations
variable {J Y : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype Y]

/-- One catalogue identity belongs to exactly one observation block. Distinct
identities may still denote correlated tests inside that block. -/
noncomputable def ownedModel (prior : Prob Ω) (channels : Ω → J → Prob Y)
    (owner : Id → J) (test : Id → Y → Bool) : Model Unit Ω (J → Y) Id where
  prior _ := prior
  observations _ w := independent (channels w)
  catalogue i ys := test i (ys (owner i))

def blockAccepts (owner : Id → J) (test : Id → Y → Bool) (E : Finset Id)
    (j : J) (y : Y) : Prop := ∀ i ∈ E, owner i = j → test i y = true

noncomputable def blockLikelihood (channel : Prob Y) (owner : Id → J)
    (test : Id → Y → Bool) (E : Finset Id) (j : J) : ℝ :=
  ∑ y, if blockAccepts owner test E j y then channel.1 y else 0

omit [Fintype B] in
/-- The product law follows from the constructed joint observation kernel. -/
theorem owned_likelihood (prior : Prob Ω) (channels : Ω → J → Prob Y)
    (owner : Id → J) (test : Id → Y → Bool) (E : Finset Id) (w : Ω) :
    (ownedModel prior channels owner test).likelihood () E w =
      ∏ j, blockLikelihood (channels w j) owner test E j := by
  classical
  have accepts (ys : J → Y) :
      (ownedModel prior channels owner test).accepts E ys = true ↔
        ∀ j, blockAccepts owner test E j (ys j) := by
    simp only [Model.accepts, ownedModel, decide_eq_true_eq, blockAccepts]
    constructor
    · intro h j i hi eq; subst j; exact h i hi
    · intro h i hi; exact h (owner i) i hi rfl
  have factor (ys : J → Y) :
      (if (ownedModel prior channels owner test).accepts E ys then
          ∏ j, (channels w j).1 (ys j) else 0) =
        ∏ j, if blockAccepts owner test E j (ys j) then (channels w j).1 (ys j) else 0 := by
    by_cases h : ∀ j, blockAccepts owner test E j (ys j)
    · simp [h, (accepts ys).mpr h]
    · have no : ¬ (ownedModel prior channels owner test).accepts E ys = true :=
        fun hh => h ((accepts ys).mp hh)
      rw [if_neg no]
      obtain ⟨j, hj⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  change (∑ ys : J → Y, if (ownedModel prior channels owner test).accepts E ys then
    ∏ j, (channels w j).1 (ys j) else 0) = _
  simp_rw [factor]
  unfold blockLikelihood
  exact (Fintype.prod_sum (fun j y =>
    if blockAccepts owner test E j y then (channels w j).1 y else 0)).symm

end OwnedObservations

section Shared
variable [Fintype H] [Fintype I] [DecidableEq I] [Fintype X]

/-- Construct the joint prior from normalized shared and conditional private laws. -/
noncomputable def jointPrior (shared : Prob H) (conditional : H → I → Prob X) : Prob (H × (I → X)) :=
  joint shared fun h => independent (conditional h)

/-- A shared block can inspect only the shared choice; a private observation
block can inspect only its own choice and the shared choice. -/
noncomputable def scopedModel {Y : Type} [Fintype Y]
    (shared : Prob H) (conditional : H → I → Prob X)
    (sharedChannel : H → Prob Y) (localChannel : H → I → X → Prob Y)
    (owner : Id → Option I) (test : Id → Y → Bool) :
    Model Unit (H × (I → X)) (Option I → Y) Id :=
  ownedModel (jointPrior shared conditional)
    (fun hx j => match j with
      | none => sharedChannel hx.1
      | some i => localChannel hx.1 i (hx.2 i)) owner test

omit [Fintype B] in
theorem scoped_likelihood {Y : Type} [Fintype Y]
    (shared : Prob H) (conditional : H → I → Prob X)
    (sharedChannel : H → Prob Y) (localChannel : H → I → X → Prob Y)
    (owner : Id → Option I) (test : Id → Y → Bool) (E : Finset Id) (hx : H × (I → X)) :
    (scopedModel shared conditional sharedChannel localChannel owner test).likelihood () E hx =
      blockLikelihood (sharedChannel hx.1) owner test E none *
        ∏ i, blockLikelihood (localChannel hx.1 i (hx.2 i)) owner test E (some i) := by
  rw [scopedModel, owned_likelihood, Fintype.prod_option]

omit [Fintype B] in
/-- Evidence factorization for the actual independently constructed model. -/
theorem scoped_mass {Y : Type} [Fintype Y]
    (shared : Prob H) (conditional : H → I → Prob X)
    (sharedChannel : H → Prob Y) (localChannel : H → I → X → Prob Y)
    (owner : Id → Option I) (test : Id → Y → Bool) (E : Finset Id) (hx : H × (I → X)) :
    spaceMass (scopedModel shared conditional sharedChannel localChannel owner test) () E hx =
      shared.1 hx.1 * blockLikelihood (sharedChannel hx.1) owner test E none *
        ∏ i, (conditional hx.1 i).1 (hx.2 i) *
          blockLikelihood (localChannel hx.1 i (hx.2 i)) owner test E (some i) := by
  rw [spaceMass, scoped_likelihood, Finset.prod_mul_distrib]
  change (shared.1 hx.1 * ∏ i, (conditional hx.1 i).1 (hx.2 i)) * _ = _
  ring

omit [Fintype B] in
/-- Private evidence can be correlated within one component; only the declared
component boundary licenses this product. Shared evidence is included once. -/
theorem evidence_commonality (shared : H → ℝ) (p : H → I → X → ℝ)
    (sharedLikelihood : H → ℝ) (localLikelihood : H → I → X → ℝ)
    (c : H → I → X → ClosureOperator (Set B)) (F : Finset (Set B)) :
    commonality (fun hx : H × (I → X) => shared hx.1 * sharedLikelihood hx.1 *
      ∏ i, p hx.1 i (hx.2 i) * localLikelihood hx.1 i (hx.2 i))
      (fun hx => joinFamily fun i => c hx.1 i (hx.2 i)) F =
    ∑ h, shared h * sharedLikelihood h *
      ∏ i, commonality (fun x => p h i x * localLikelihood h i x) (c h i) F := by
  simp only [commonality, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  have factor := commonality_family (fun i x => p h i x * localLikelihood h i x) (c h) F
  unfold commonality at factor
  rw [← factor]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  congr 2
  exact Subsingleton.elim _ _

omit [Fintype B] in
/-- The empty row retains the shared-regime evidence likelihood. -/
theorem evidence_normalizer (shared : H → ℝ) (p : H → I → X → ℝ)
    (sharedLikelihood : H → ℝ) (localLikelihood : H → I → X → ℝ)
    (c : H → I → X → ClosureOperator (Set B)) :
    commonality (fun hx : H × (I → X) => shared hx.1 * sharedLikelihood hx.1 *
      ∏ i, p hx.1 i (hx.2 i) * localLikelihood hx.1 i (hx.2 i))
      (fun hx => joinFamily fun i => c hx.1 i (hx.2 i)) ∅ =
    ∑ h, shared h * sharedLikelihood h * ∏ i, ∑ x, p h i x * localLikelihood h i x := by
  rw [evidence_commonality]
  simp only [commonality_empty]

end Shared
namespace Controls

/-- Idempotent evidence replay cannot be read as multiplication of posterior
probabilities strictly between zero and one. -/
noncomputable def badPosteriorReading : WMReading Bool Unit ℝ where
  revise := (· || ·)
  extract s _ := if s then 2/3 else 1/2
  combine := (· * ·)
  zero := 1
  world _ := false
  query _ := ()

theorem posterior_not_multiplicative : ¬ badPosteriorReading.CoreLaws := by
  intro laws
  have h := laws.extract_revise true true ()
  norm_num [badPosteriorReading] at h

/-- Discarding regime-specific evidence normalizers leaves the prior unchanged. -/
def prematureAnswer : ℚ :=
  let likelihood := fun h : Bool => if h then (3/4 : ℚ) else 1/4
  let normalized := fun h => likelihood h / likelihood h
  (∑ h : Bool, if h then (1/2 : ℚ) * normalized h ^ 2 else 0) /
    (∑ h : Bool, (1/2 : ℚ) * normalized h ^ 2)

theorem premature_normalization_wrong : prematureAnswer = 1/2 ∧ prematureAnswer ≠ 9/10 := by
  decide +kernel

end Controls
end Mettapedia.Logic.RandomClosure.DistributionalEvidence
