import Mettapedia.GSLT.Distinction.Probabilistic.Controls
import Mettapedia.GSLT.Logic.GradedSupport
import Mettapedia.Cybernetics.ApproximateAdequacy.Weighting
import Mathlib.Data.NNReal.Basic

/-!
# Semiring-weighted GSLTs: probabilistic and possibilistic instances

**One definition** (`WeightedSystem S K`): over a GSLT `S` and a semiring `K`
of coefficients, every labelled step is a finitely supported family of
coefficients on successor terms, read modulo the equations: equated sources
give every equation-closed set of successors the same sum (`kernel_resp`).

* **Change of coefficients** (`mapCoefficients`) along a semiring map keeps
  the equations: sums over closed sets are mapped (`closedSum_mapRange`).
* **The support erasure** (`WeightedSystem.support`) is a
  `HennessyMilner.System` whenever the coefficients cannot cancel
  (`GSLT.GradedSupport.NoCancellation`), so that a closed set has a nonzero sum
  exactly when it holds a supported successor (`closedSum_ne_zero_iff`).
* **The Boolean instance.**  On the Boolean semiring `OrBool` (disjunction and
  conjunction) a weighted system is a finitely branching possibilistic system.
  For every algebra that cannot cancel, "is nonzero" is a semiring map into
  `OrBool` (`supportHom`), and **the support erasure is the image of the
  coefficients in the Boolean semiring** (`support_mapCoefficients_supportHom`).
* **The probability instance.**  A probabilistic GSLT is a weighted system
  over the probability semiring `ℝ≥0` (`ProbabilisticSystem.toWeighted`) with
  the same masses (`coe_closedSum_toWeighted`) and the same support
  (`support_toWeighted`); conversely a weighted system over `ℝ≥0` whose steps
  have total at most one is a probabilistic GSLT (`WeightedSystem.toProbabilistic`,
  `prob_toProbabilistic`).  Hence the possibilistic erasure of a probabilistic
  GSLT is the Boolean image of its coefficients
  (`ProbabilisticSystem.support_eq_boolean_image`).

**Coefficients are not observer weights** (`observerReading`).  Observer
importance is a finite weighting of observers (`ApproximateAdequacy.FiniteWeighting`
on formulas); a weighted reading charges the observers that separate two terms.
It reads only the erasure (`observerReading_eq_of_support_eq`), so it is blind
to coefficients that keep the supports: in `Controls` the fair and the biased
coin have different coefficients and every weighted reading of support
observers gives them disagreement zero (`coins_observerReading_zero`), while a
weighted reading of Larsen–Skou observers charging one probabilistic formula
separates them (`coins_lsObserverReading_pos`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.GradedSupport
open Mettapedia.Cybernetics.ApproximateAdequacy (FiniteWeighting)
open scoped NNReal

universe uS uAtom uLabel uK uL

/-! ## Sums over closed sets -/

section ClosedSum

variable {α : Type*} {K : Type*} [AddCommMonoid K]

open Classical in
/-- The sum of the coefficients on a predicate. -/
noncomputable def closedSum (f : α →₀ K) (C : α → Prop) : K :=
  ∑ x ∈ f.support, if C x then f x else 0

theorem finset_sum_eq_zero_iff {K : Type*} [Semiring K] (noCancel : NoCancellation K)
    {ι : Type*} (s : Finset ι) (g : ι → K) : ∑ i ∈ s, g i = 0 ↔ ∀ i ∈ s, g i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s outside ih =>
      rw [Finset.sum_insert outside]
      constructor
      · intro zero
        have head : g a = 0 := noCancel.add_eq_zero _ _ zero
        have tail : ∑ i ∈ s, g i = 0 := noCancel.add_eq_zero _ _ (by rw [add_comm]; exact zero)
        intro i member
        rcases Finset.mem_insert.mp member with rfl | inside
        · exact head
        · exact ih.mp tail i inside
      · intro all
        rw [all a (Finset.mem_insert_self a s), ih.mpr fun i member =>
          all i (Finset.mem_insert_of_mem member), add_zero]

/-- **Without cancellation, a closed set has a nonzero sum exactly when it holds
a supported point.** -/
theorem closedSum_ne_zero_iff {K : Type*} [Semiring K] (noCancel : NoCancellation K)
    (f : α →₀ K) (C : α → Prop) : closedSum f C ≠ 0 ↔ ∃ x ∈ f.support, C x := by
  classical
  unfold closedSum
  rw [Ne, finset_sum_eq_zero_iff noCancel]
  constructor
  · intro notAll
    push Not at notAll
    obtain ⟨x, member, nonzero⟩ := notAll
    by_cases holds : C x
    · exact ⟨x, member, holds⟩
    · rw [if_neg holds] at nonzero
      exact absurd rfl nonzero
  · rintro ⟨x, member, holds⟩ all
    have := all x member
    rw [if_pos holds] at this
    exact Finsupp.mem_support_iff.mp member this

/-- **Sums over closed sets are mapped along additive maps.** -/
theorem closedSum_mapRange {L : Type*} [AddCommMonoid L] (φ : K →+ L) (f : α →₀ K)
    (C : α → Prop) : closedSum (Finsupp.mapRange φ φ.map_zero f) C = φ (closedSum f C) := by
  classical
  unfold closedSum
  have extend : ∑ x ∈ (Finsupp.mapRange φ φ.map_zero f).support,
      (if C x then Finsupp.mapRange φ φ.map_zero f x else 0) =
      ∑ x ∈ f.support, (if C x then Finsupp.mapRange φ φ.map_zero f x else 0) := by
    refine Finset.sum_subset Finsupp.support_mapRange fun x _ outside => ?_
    rw [Finsupp.notMem_support_iff] at outside
    rw [outside]
    simp
  rw [extend, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.mapRange_apply]
  split_ifs
  · rfl
  · exact (map_zero φ).symm

end ClosedSum

/-! ## Weighted systems -/

set_option linter.checkUnivs false in
/-- **A semiring-weighted system over a GSLT**: atomic observations and labelled
steps, each a finitely supported family of coefficients on successor terms,
read modulo the equations. -/
structure WeightedSystem.{uS', uK', uAtom', uLabel'} (S : GSLT.{uS'}) (K : Type uK') [Semiring K]
    where
  /-- The observation set. -/
  Atom : Type uAtom'
  /-- Atomic observations. -/
  observes : Atom → S.Term → Prop
  observes_resp : ∀ (atom : Atom) {left right : S.Term},
    S.Equiv left right → (observes atom left ↔ observes atom right)
  /-- The labels. -/
  Label : Type uLabel'
  /-- The coefficients of the successors of a labelled step. -/
  kernel : Label → S.Term → S.Term →₀ K
  /-- **The coefficients are read modulo the equations.** -/
  kernel_resp : ∀ (label : Label) {left right : S.Term}, S.Equiv left right →
    ∀ C : S.Term → Prop, (∀ x y, S.Equiv x y → (C x ↔ C y)) →
      closedSum (kernel label left) C = closedSum (kernel label right) C

namespace WeightedSystem

variable {S : GSLT.{uS}} {K : Type uK} [Semiring K]

/-- **Change of coefficients** along a semiring map. -/
noncomputable def mapCoefficients {L : Type uL} [Semiring L]
    (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K) (φ : K →+* L) :
    WeightedSystem.{uS, uL, uAtom, uLabel} S L where
  Atom := W.Atom
  observes := W.observes
  observes_resp := W.observes_resp
  Label := W.Label
  kernel label source := Finsupp.mapRange φ φ.map_zero (W.kernel label source)
  kernel_resp label left right equivalent C closed := by
    have mapped := fun source => closedSum_mapRange φ.toAddMonoidHom (W.kernel label source) C
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at mapped
    rw [mapped, mapped, W.kernel_resp label equivalent C closed]

/-- **The support erasure** of a weighted system whose coefficients cannot
cancel: a step goes to every term equated to a supported successor. -/
def support (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K) (noCancel : NoCancellation K) :
    System.{uAtom, uLabel} S where
  Atom := W.Atom
  observes := W.observes
  observes_resp := W.observes_resp
  Label := W.Label
  act label source target := ∃ x ∈ (W.kernel label source).support, S.Equiv x target
  act_resp_left := by
    intro label left right target equivalent ⟨x, member, close⟩
    have nonzero : closedSum (W.kernel label left) (S.Equiv · target) ≠ 0 :=
      (closedSum_ne_zero_iff noCancel _ _).mpr ⟨x, member, close⟩
    rw [W.kernel_resp label equivalent _ (ProbabilisticSystem.equiv_closed target)] at nonzero
    obtain ⟨x', member', close'⟩ := (closedSum_ne_zero_iff noCancel _ _).mp nonzero
    exact ⟨target, ⟨x', member', close'⟩, S.equations.iseqv.refl target⟩
  act_resp_right := by
    intro label source target target' ⟨x, member, close⟩ equivalent
    exact ⟨x, member, S.equations.iseqv.trans close equivalent⟩

/-- Systems with the same observations, labels and step supports have the same
support erasure. -/
theorem support_eq_of_supports {K' : Type uL} [Semiring K']
    (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K)
    (W' : WeightedSystem.{uS, uL, uAtom, uLabel} S K')
    (noCancel : NoCancellation K) (noCancel' : NoCancellation K')
    (atoms : W.Atom = W'.Atom) (labels : W.Label = W'.Label)
    (observations : HEq W.observes W'.observes)
    (supports : HEq (fun label source => (W.kernel label source).support)
      (fun label source => (W'.kernel label source).support)) :
    W.support noCancel = W'.support noCancel' := by
  obtain ⟨Atom, observes, observes_resp, Label, kernel, kernel_resp⟩ := W
  obtain ⟨Atom', observes', observes_resp', Label', kernel', kernel_resp'⟩ := W'
  subst atoms labels
  cases observations
  have same : (fun label source => (kernel label source).support) =
      fun label source => (kernel' label source).support := eq_of_heq supports
  unfold support
  simp only
  congr 1
  funext label source target
  rw [show (kernel label source).support = (kernel' label source).support from
    congrFun (congrFun same label) source]

/-! ## The Boolean semiring -/

/-- **"Is nonzero" is a semiring map into the Boolean semiring** for an algebra
that cannot cancel. -/
noncomputable def supportHom (K : Type uK) [Semiring K] (noCancel : NoCancellation K) :
    K →+* OrBool where
  toFun x := ⟨@decide (x ≠ 0) (Classical.propDecidable _)⟩
  map_one' := by
    apply OrBool.ext'
    change @decide ((1 : K) ≠ 0) (Classical.propDecidable _) = true
    simp [noCancel.one_ne_zero]
  map_zero' := by
    apply OrBool.ext'
    change @decide ((0 : K) ≠ 0) (Classical.propDecidable _) = false
    simp
  map_add' a b := by
    apply OrBool.ext'
    change @decide (a + b ≠ 0) (Classical.propDecidable _) =
      (@decide (a ≠ 0) (Classical.propDecidable _) || @decide (b ≠ 0) (Classical.propDecidable _))
    have zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 :=
      ⟨fun sum => ⟨noCancel.add_eq_zero a b sum,
        noCancel.add_eq_zero b a (by rw [add_comm]; exact sum)⟩,
        fun ⟨first, second⟩ => by rw [first, second, add_zero]⟩
    by_cases first : a = 0 <;> by_cases second : b = 0 <;> simp [first, second, zero_iff]
  map_mul' a b := by
    apply OrBool.ext'
    change @decide (a * b ≠ 0) (Classical.propDecidable _) =
      (@decide (a ≠ 0) (Classical.propDecidable _) && @decide (b ≠ 0) (Classical.propDecidable _))
    have zero_iff : a * b = 0 ↔ a = 0 ∨ b = 0 :=
      ⟨noCancel.mul_eq_zero a b, fun zero => by
        rcases zero with first | second
        · rw [first, zero_mul]
        · rw [second, mul_zero]⟩
    by_cases first : a = 0 <;> by_cases second : b = 0 <;> simp [first, second, zero_iff]

theorem supportHom_eq_zero_iff (K : Type uK) [Semiring K] (noCancel : NoCancellation K) (x : K) :
    supportHom K noCancel x = 0 ↔ x = 0 := by
  constructor
  · intro zero
    by_contra nonzero
    have value := congrArg OrBool.val zero
    change @decide (x ≠ 0) (Classical.propDecidable _) = false at value
    simp [nonzero] at value
  · intro zero
    rw [zero, map_zero]

/-- **The support erasure is the image of the coefficients in the Boolean
semiring.** -/
theorem support_mapCoefficients_supportHom (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K)
    (noCancel : NoCancellation K) :
    (W.mapCoefficients (supportHom K noCancel)).support OrBool.noCancellation =
      W.support noCancel := by
  refine support_eq_of_supports _ _ _ _ rfl rfl HEq.rfl (heq_of_eq ?_)
  funext label source
  ext x
  simp only [mapCoefficients, Finsupp.mem_support_iff, Finsupp.mapRange_apply, Ne,
    supportHom_eq_zero_iff]

/-- **Satisfaction in the support erasure is unchanged by a change of
coefficients that reflects zero.** -/
theorem sat_support_mapCoefficients {L : Type uL} [Semiring L]
    (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K) (φ : K →+* L)
    (reflects : ∀ x, φ x = 0 → x = 0) (noCancel : NoCancellation K)
    (noCancel' : NoCancellation L) :
    ∀ (formula : Formula W.Atom W.Label) (term : S.Term),
      ((W.mapCoefficients φ).support noCancel').sat formula term ↔
        (W.support noCancel).sat formula term
  | .top, _ => Iff.rfl
  | .atom _, _ => Iff.rfl
  | .conj left right, term => and_congr (sat_support_mapCoefficients W φ reflects noCancel
      noCancel' left term) (sat_support_mapCoefficients W φ reflects noCancel noCancel' right term)
  | .neg inner, term => not_congr
      (sat_support_mapCoefficients W φ reflects noCancel noCancel' inner term)
  | .dia label inner, term => by
      have supports : ∀ x, x ∈ ((W.mapCoefficients φ).kernel label term).support ↔
          x ∈ (W.kernel label term).support := fun x => by
        simp only [mapCoefficients, Finsupp.mem_support_iff, Finsupp.mapRange_apply, Ne]
        exact ⟨fun nonzero zero => nonzero (by rw [zero, map_zero]),
          fun nonzero zero => nonzero (reflects _ zero)⟩
      constructor
      · rintro ⟨target, ⟨x, member, close⟩, holds⟩
        exact ⟨target, ⟨x, (supports x).mp member, close⟩,
          (sat_support_mapCoefficients W φ reflects noCancel noCancel' inner target).mp holds⟩
      · rintro ⟨target, ⟨x, member, close⟩, holds⟩
        exact ⟨target, ⟨x, (supports x).mpr member, close⟩,
          (sat_support_mapCoefficients W φ reflects noCancel noCancel' inner target).mpr holds⟩

end WeightedSystem

/-! ## The probability semiring -/

/-- The probability semiring cannot cancel. -/
theorem nnreal_noCancellation : NoCancellation ℝ≥0 where
  add_eq_zero _ _ sum := (add_eq_zero.mp sum).1
  mul_eq_zero _ _ product := mul_eq_zero.mp product
  one_ne_zero := one_ne_zero

namespace ProbabilisticSystem

variable {S : GSLT.{uS}} (M : ProbabilisticSystem.{uS, uAtom, uLabel} S)

/-- The weights of a sub-distribution, in the probability semiring. -/
noncomputable def nnWeight (μ : SubDistribution S.Term) : S.Term →₀ ℝ≥0 :=
  Finsupp.mapRange Real.toNNReal Real.toNNReal_zero μ.weight

theorem support_nnWeight (μ : SubDistribution S.Term) : (nnWeight μ).support = μ.weight.support := by
  ext x
  simp only [nnWeight, Finsupp.mem_support_iff, Finsupp.mapRange_apply, Ne,
    Real.toNNReal_eq_zero]
  exact ⟨fun positive zero => positive (zero ▸ le_rfl),
    fun nonzero nonpos => nonzero (le_antisymm nonpos (μ.nonneg x))⟩

theorem coe_closedSum_nnWeight (μ : SubDistribution S.Term) (C : S.Term → Prop) :
    ((closedSum (nnWeight μ) C : ℝ≥0) : ℝ) = μ.mass C := by
  classical
  unfold closedSum SubDistribution.mass
  rw [support_nnWeight, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · simp [nnWeight, Real.coe_toNNReal _ (μ.nonneg x)]
  · rfl

/-- **A probabilistic GSLT is a weighted system over the probability
semiring.** -/
noncomputable def toWeighted : WeightedSystem.{uS, 0, uAtom, uLabel} S ℝ≥0 where
  Atom := M.Atom
  observes := M.observes
  observes_resp := M.observes_resp
  Label := M.Label
  kernel label source := nnWeight (M.kernel label source)
  kernel_resp label left right equivalent C closed := by
    apply NNReal.coe_injective
    rw [coe_closedSum_nnWeight, coe_closedSum_nnWeight]
    exact M.kernel_resp label equivalent C closed

/-- The coefficient sums of a probabilistic GSLT are its masses. -/
theorem coe_closedSum_toWeighted (label : M.Label) (source : S.Term) (C : S.Term → Prop) :
    ((closedSum ((M.toWeighted).kernel label source) C : ℝ≥0) : ℝ) = M.prob label source C :=
  coe_closedSum_nnWeight _ C

/-- **The weighted support erasure is the probabilistic one.** -/
theorem support_toWeighted : (M.toWeighted).support nnreal_noCancellation = M.support := by
  unfold WeightedSystem.support ProbabilisticSystem.support
  simp only [toWeighted, support_nnWeight]

/-- **The possibilistic erasure of a probabilistic GSLT is the image of its
coefficients in the Boolean semiring.** -/
theorem support_eq_boolean_image :
    ((M.toWeighted).mapCoefficients (WeightedSystem.supportHom ℝ≥0 nnreal_noCancellation)).support
        OrBool.noCancellation = M.support := by
  rw [WeightedSystem.support_mapCoefficients_supportHom, support_toWeighted]

end ProbabilisticSystem

namespace WeightedSystem

variable {S : GSLT.{uS}}

/-- The real weights of a family in the probability semiring. -/
noncomputable def realWeight (f : S.Term →₀ ℝ≥0) : S.Term →₀ ℝ :=
  Finsupp.mapRange ((↑) : ℝ≥0 → ℝ) NNReal.coe_zero f

theorem support_realWeight (f : S.Term →₀ ℝ≥0) : (realWeight f).support = f.support := by
  ext x
  simp [realWeight]

/-- The sub-distribution of a family in the probability semiring with total at
most one. -/
noncomputable def realSub (f : S.Term →₀ ℝ≥0) (total : ∑ x ∈ f.support, ((f x : ℝ≥0) : ℝ) ≤ 1) :
    SubDistribution S.Term where
  weight := realWeight f
  nonneg x := by simp [realWeight]
  total_le_one := by
    rw [support_realWeight]
    simpa [realWeight] using total

theorem mass_realSub (f : S.Term →₀ ℝ≥0) (total : ∑ x ∈ f.support, ((f x : ℝ≥0) : ℝ) ≤ 1)
    (C : S.Term → Prop) : (realSub f total).mass C = ((closedSum f C : ℝ≥0) : ℝ) := by
  classical
  unfold SubDistribution.mass closedSum
  change (∑ x ∈ (realWeight f).support, if C x then realWeight f x else 0) = _
  rw [support_realWeight, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [realWeight]

/-- **A weighted system over the probability semiring whose steps have total
at most one is a probabilistic GSLT.** -/
noncomputable def toProbabilistic (W : WeightedSystem.{uS, 0, uAtom, uLabel} S ℝ≥0)
    (total : ∀ label source, ∑ x ∈ (W.kernel label source).support,
      ((W.kernel label source x : ℝ≥0) : ℝ) ≤ 1) :
    ProbabilisticSystem.{uS, uAtom, uLabel} S where
  Atom := W.Atom
  observes := W.observes
  observes_resp := W.observes_resp
  Label := W.Label
  kernel label source := realSub (W.kernel label source) (total label source)
  kernel_resp label left right equivalent C closed := by
    rw [mass_realSub, mass_realSub, W.kernel_resp label equivalent C closed]

/-- The masses of the probabilistic GSLT are the coefficient sums. -/
theorem prob_toProbabilistic (W : WeightedSystem.{uS, 0, uAtom, uLabel} S ℝ≥0)
    (total : ∀ label source, ∑ x ∈ (W.kernel label source).support,
      ((W.kernel label source x : ℝ≥0) : ℝ) ≤ 1) (label : W.Label) (source : S.Term)
    (C : S.Term → Prop) :
    (W.toProbabilistic total).prob label source C =
      ((closedSum (W.kernel label source) C : ℝ≥0) : ℝ) :=
  mass_realSub (W.kernel label source) (total label source) C

end WeightedSystem

/-! ## Coefficients are not observer weights -/

section Observers

variable {S : GSLT.{uS}}

open Classical in
/-- **A weighted reading of support observers**: observer importance is a
finite weighting of Hennessy–Milner formulas, and the reading charges the
formulas that separate two terms.  It reads the support erasure only. -/
noncomputable def observerReading (N : System.{uAtom, uLabel} S)
    (weights : FiniteWeighting ℝ (Formula N.Atom N.Label)) (left right : S.Term) : ℝ :=
  weights.expectation fun formula => if (N.sat formula left ↔ N.sat formula right) then 0 else 1

open Classical in
/-- **A weighted reading of Larsen–Skou observers.** -/
noncomputable def lsObserverReading (M : ProbabilisticSystem.{uS, uAtom, uLabel} S)
    (weights : FiniteWeighting ℝ (ProbabilisticSystem.LSFormula M.Atom M.Label))
    (left right : S.Term) : ℝ :=
  weights.expectation fun formula => if (M.sat formula left ↔ M.sat formula right) then 0 else 1

/-- **Observer weights read only the erasure**: a change of coefficients that
reflects zero, such as the passage to the Boolean semiring, changes no reading,
for every observer weighting. -/
theorem observerReading_mapCoefficients {K : Type uK} [Semiring K] {L : Type uL} [Semiring L]
    (W : WeightedSystem.{uS, uK, uAtom, uLabel} S K) (φ : K →+* L)
    (reflects : ∀ x, φ x = 0 → x = 0) (noCancel : NoCancellation K)
    (noCancel' : NoCancellation L) (weights : FiniteWeighting ℝ (Formula W.Atom W.Label))
    (left right : S.Term) :
    observerReading ((W.mapCoefficients φ).support noCancel') weights left right =
      observerReading (W.support noCancel) weights left right := by
  classical
  unfold observerReading FiniteWeighting.expectation
  refine Finset.sum_congr rfl fun formula _ => ?_
  have same := iff_congr
    (WeightedSystem.sat_support_mapCoefficients W φ reflects noCancel noCancel' formula left)
    (WeightedSystem.sat_support_mapCoefficients W φ reflects noCancel noCancel' formula right)
  beta_reduce
  split_ifs with mapped original original
  · rfl
  · exact absurd (same.mp mapped) original
  · exact absurd (same.mpr original) mapped
  · rfl

/-- Bisimilar terms are at reading zero for every observer weighting. -/
theorem observerReading_eq_zero_of_bisimilar (N : System.{uAtom, uLabel} S)
    (weights : FiniteWeighting ℝ (Formula N.Atom N.Label)) {left right : S.Term}
    (bisimilar : N.Bisimilar left right) : observerReading N weights left right = 0 := by
  classical
  unfold observerReading FiniteWeighting.expectation
  refine Finset.sum_eq_zero fun formula _ => ?_
  simp only [if_pos (N.logicallyEquivalent_of_bisimilar bisimilar formula), mul_zero]

end Observers

/-! ## The coins: coefficients invisible to support observers -/

section Coins

open Controls

/-- **Every weighted reading of support observers gives the coins disagreement
zero**: their coefficients differ, their support erasures agree. -/
theorem coins_observerReading_zero
    (weights : FiniteWeighting ℝ (Formula (chainSystem chain).support.Atom
      (chainSystem chain).support.Label)) :
    observerReading (chainSystem chain).support weights Point.fair Point.biased = 0 :=
  observerReading_eq_zero_of_bisimilar _ weights fair_biased_support_bisimilar

/-- The weighting of Larsen–Skou observers that charges only "more than `1/3`
reaches the observable". -/
noncomputable def oneThirdObserver :
    FiniteWeighting ℝ (ProbabilisticSystem.LSFormula (chainSystem chain).Atom
      (chainSystem chain).Label) where
  support := {.more () (1 / 3) (.atom ((), 1))}
  weight _ := 1
  nonneg _ _ := zero_le_one
  sum_eq_one := by simp

/-- **A weighted reading of Larsen–Skou observers separates the coins.** -/
theorem coins_lsObserverReading_pos :
    lsObserverReading (chainSystem chain) oneThirdObserver Point.fair Point.biased = 1 := by
  classical
  have holds : (chainSystem chain).sat (.more () (1 / 3) (.atom ((), 1))) Point.fair := by
    change ((1 / 3 : ℚ) : ℝ) < _
    rw [fair_prob]
    norm_num
  have fails : ¬ (chainSystem chain).sat (.more () (1 / 3) (.atom ((), 1))) Point.biased := by
    change ¬ ((1 / 3 : ℚ) : ℝ) < _
    rw [biased_prob]
    norm_num
  unfold lsObserverReading FiniteWeighting.expectation oneThirdObserver
  simp only [Finset.sum_singleton, one_mul]
  rw [if_neg fun same => fails (same.mp holds)]

end Coins

end Mettapedia.GSLT.Distinction.Probabilistic
