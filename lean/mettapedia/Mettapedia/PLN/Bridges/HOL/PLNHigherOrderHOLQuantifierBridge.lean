import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierSemantics
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSemanticsFin
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSoundnessInf
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierAlgorithmTheorems

/-!
# Higher-Order HOL Quantifier Bridge

This file is the live HOL-facing version of PLN's satisfying-set reduction for
quantifiers. A HOL unary predicate over a Henkin model induces the existing
finite-domain `PLNFirstOrder.SatisfyingSet` over admissible predicate objects.
The quantifier and QFM layers can then consume that satisfying set directly,
instead of duplicating a higher-order quantifier semantics beside it.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The finite satisfying-set reduction for a HOL unary predicate at a pointed
Henkin model. Its carrier is the type of admissible objects for the quantified
HOL type, and its predicate is the crisp p-bit view of HOL satisfaction. -/
noncomputable def predicateSatisfyingSet
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    SatisfyingSet (PredicateObject (Base := Base) (Const := Const) M σ) :=
  ⟨fun x => by
    classical
    exact
    if predicateHoldsAt (Base := Base) (Const := Const) M σ p x then
      pTrue
    else
      pFalse⟩

/-- Membership in the HOL-induced satisfying set is exactly model satisfaction
of the predicate at the admissible object. -/
theorem predicateSatisfyingSet_isTrue_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isTrue ((predicateSatisfyingSet
      (Base := Base) (Const := Const) M σ p).pred x) ↔
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  classical
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simpa [predicateSatisfyingSet, hx] using pTrue_isTrue
  · simp [predicateSatisfyingSet, hx,
      Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isTrue, pFalse]

/-- The comprehension set of the induced first-order satisfying set is the HOL
predicate extension over admissible objects. -/
theorem predicateSatisfyingSet_mem_comprehension_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    x ∈ (predicateSatisfyingSet
      (Base := Base) (Const := Const) M σ p).comprehension ↔
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  simpa [SatisfyingSet.mem_comprehension] using
    predicateSatisfyingSet_isTrue_iff
      (Base := Base) (Const := Const) M σ p x

/-- The diagonal used by first-order PLN quantifiers is exactly the pairwise
HOL satisfying-set diagonal. -/
theorem predicateSatisfyingSet_mem_diagonal_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (xy : PredicateObject (Base := Base) (Const := Const) M σ ×
      PredicateObject (Base := Base) (Const := Const) M σ) :
    xy ∈ (predicateSatisfyingSet
      (Base := Base) (Const := Const) M σ p).diagonal ↔
        predicateHoldsAt (Base := Base) (Const := Const) M σ p xy.1 ∧
          predicateHoldsAt (Base := Base) (Const := Const) M σ p xy.2 := by
  rw [SatisfyingSet.mem_diagonal]
  simp [predicateSatisfyingSet_isTrue_iff
    (Base := Base) (Const := Const) M σ p]

/-- HOL universal predicate truth is the same as universal truth over the
induced first-order satisfying set. -/
theorem models_predicateForAllFormula_iff_satisfyingSet_all
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isTrue ((predicateSatisfyingSet
          (Base := Base) (Const := Const) M σ p).pred x) := by
  rw [models_predicateForAllFormula_iff]
  constructor
  · intro h x
    exact
      (predicateSatisfyingSet_isTrue_iff
        (Base := Base) (Const := Const) M σ p x).2 (h x)
  · intro h x
    exact
      (predicateSatisfyingSet_isTrue_iff
        (Base := Base) (Const := Const) M σ p x).1 (h x)

/-- HOL existential predicate truth is the same as existential truth over the
induced first-order satisfying set. -/
theorem models_predicateExistsFormula_iff_satisfyingSet_exists
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M
        (predicateExistsFormula (Base := Base) (Const := Const) σ p) ↔
      ∃ x : PredicateObject (Base := Base) (Const := Const) M σ,
        Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isTrue ((predicateSatisfyingSet
          (Base := Base) (Const := Const) M σ p).pred x) := by
  rw [models_predicateExistsFormula_iff]
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact
      ⟨x, (predicateSatisfyingSet_isTrue_iff
        (Base := Base) (Const := Const) M σ p x).2 hx⟩
  · intro h
    rcases h with ⟨x, hx⟩
    exact
      ⟨x, (predicateSatisfyingSet_isTrue_iff
        (Base := Base) (Const := Const) M σ p x).1 hx⟩

/-- HOL universal predicate truth says exactly that every admissible object
belongs to the HOL-induced satisfying-set comprehension. -/
theorem models_predicateForAllFormula_iff_satisfyingSet_comprehension_all
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        x ∈ (predicateSatisfyingSet
          (Base := Base) (Const := Const) M σ p).comprehension := by
  rw [models_predicateForAllFormula_iff_satisfyingSet_all]
  constructor
  · intro h x
    exact
      (SatisfyingSet.mem_comprehension
        (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) x).2
        (h x)
  · intro h x
    exact
      (SatisfyingSet.mem_comprehension
        (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) x).1
        (h x)

/-- HOL existential predicate truth is the book's `NonEmpty(SatisfyingSet P)`
condition: the HOL-induced satisfying-set comprehension has a witness. -/
theorem models_predicateExistsFormula_iff_satisfyingSet_nonempty
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M
        (predicateExistsFormula (Base := Base) (Const := Const) σ p) ↔
      ((predicateSatisfyingSet
        (Base := Base) (Const := Const) M σ p).comprehension).Nonempty := by
  rw [models_predicateExistsFormula_iff_satisfyingSet_exists]
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact
      ⟨x,
        (SatisfyingSet.mem_comprehension
          (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) x).2
          hx⟩
  · intro h
    rcases h with ⟨x, hx⟩
    exact
      ⟨x,
        (SatisfyingSet.mem_comprehension
          (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) x).1
          hx⟩

/-- PLN weakness/diagonal evaluation of universal truth for a HOL predicate,
reusing the existing first-order quantifier semantics. -/
noncomputable def predicateForAllEval
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (μ : WeightFunction
      (PredicateObject (Base := Base) (Const := Const) M σ) BinaryEvidence) :
    BinaryEvidence :=
  forAllEval
    (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) μ

/-- PLN De-Morgan/weakness evaluation of existential truth for a HOL predicate,
reusing the existing first-order quantifier semantics. -/
noncomputable def predicateExistsEval
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (μ : WeightFunction
      (PredicateObject (Base := Base) (Const := Const) M σ) BinaryEvidence) :
    BinaryEvidence :=
  thereExistsEval
    (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) μ

@[simp] theorem predicateForAllEval_eq_forAllEval
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (μ : WeightFunction
      (PredicateObject (Base := Base) (Const := Const) M σ) BinaryEvidence) :
    predicateForAllEval (Base := Base) (Const := Const) M σ p μ =
      forAllEval
        (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) μ :=
  rfl

@[simp] theorem predicateExistsEval_eq_thereExistsEval
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (μ : WeightFunction
      (PredicateObject (Base := Base) (Const := Const) M σ) BinaryEvidence) :
    predicateExistsEval (Base := Base) (Const := Const) M σ p μ =
      thereExistsEval
        (predicateSatisfyingSet (Base := Base) (Const := Const) M σ p) μ :=
  rfl

/-- Crisp `[0,1]` profile induced by a HOL predicate over admissible objects.
This is the finite-domain QFM view of the same satisfying-set reduction. -/
noncomputable def predicateCrispProfile
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    PredicateObject (Base := Base) (Const := Const) M σ → ℝ :=
  fun x => by
    classical
    exact
    if predicateHoldsAt (Base := Base) (Const := Const) M σ p x then
      1
    else
      0

theorem predicateCrispProfile_mem_unit
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x ∈
      Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [predicateCrispProfile, hx]
  · simp [predicateCrispProfile, hx]

theorem predicateCrispProfile_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x ≤ 1 :=
  (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p x).2

theorem predicateCrispProfile_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x ≤
      predicateCrispProfile (Base := Base) (Const := Const) M σ q x := by
  classical
  have hPoint :=
    (predicateInterpretation_inherits_iff
      (Base := Base) (Const := Const) M σ p q).1 hInh
  by_cases hp : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · have hq : predicateHoldsAt (Base := Base) (Const := Const) M σ q x :=
      hPoint x hp
    simp [predicateCrispProfile, hp, hq]
  · by_cases hq : predicateHoldsAt (Base := Base) (Const := Const) M σ q x
    · simp [predicateCrispProfile, hp, hq]
    · simp [predicateCrispProfile, hp, hq]

/-- Pointwise-equivalent HOL predicates induce the same finite QFM crisp
profile. -/
theorem predicateCrispProfile_eq_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p =
      predicateCrispProfile (Base := Base) (Const := Const) M σ q := by
  funext x
  classical
  by_cases hp : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · have hq := (hiff x).1 hp
    simp [predicateCrispProfile, hp, hq]
  · have hq :
        ¬ predicateHoldsAt (Base := Base) (Const := Const) M σ q x := by
      intro hq
      exact hp ((hiff x).2 hq)
    simp [predicateCrispProfile, hp, hq]

/-- The crisp HOL-induced QFM profile has value `1` exactly on satisfying
objects. -/
theorem predicateCrispProfile_eq_one_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x = 1 ↔
      predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  classical
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [predicateCrispProfile, hx]
  · simp [predicateCrispProfile, hx]

/-- The crisp HOL-induced QFM profile has value `0` exactly off the
satisfying extension. -/
theorem predicateCrispProfile_eq_zero_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x = 0 ↔
      ¬ predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  classical
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [predicateCrispProfile, hx]
  · simp [predicateCrispProfile, hx]

/-- The finite-domain QFM `ForAll` rule is reused directly: predicate
inheritance induces pointwise profile monotonicity, which preserves QFM
universal truth. -/
theorem predicateFuzzyForAllHolds_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (hAll :
      fuzzyForAllHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p)) :
    fuzzyForAllHolds params
      (predicateCrispProfile (Base := Base) (Const := Const) M σ q) := by
  exact
    fuzzyForAllHolds_mono_of_pointwise
      params
      (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
      (predicateCrispProfile (Base := Base) (Const := Const) M σ q)
      (predicateCrispProfile_mono_of_inherits
        (Base := Base) (Const := Const) M σ p q hInh)
      (predicateCrispProfile_le_one
        (Base := Base) (Const := Const) M σ q)
      hAll

/-- Relaxing the QFM tolerance and `PCL` threshold preserves HOL-predicate
`ForAll` acceptance, by the existing Chapter-11 finite-QFM theorem. -/
theorem predicateFuzzyForAllHolds_of_epsilon_and_PCL_relax
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params₁ params₂ : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε : params₁.ε ≤ params₂.ε)
    (hPCL : params₂.PCL ≤ params₁.PCL)
    (hAll :
      fuzzyForAllHolds params₁
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p)) :
    fuzzyForAllHolds params₂
      (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyForAllHolds_of_epsilon_and_PCL_relax
    params₁ params₂
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hε hPCL hAll

/-- With fixed tolerance, lowering `PCL` preserves HOL-predicate QFM
`ForAll` acceptance. -/
theorem predicateFuzzyForAllHolds_of_lowerPCL_sameEpsilon
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params₁ params₂ : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε : params₁.ε = params₂.ε)
    (hPCL : params₂.PCL ≤ params₁.PCL)
    (hAll :
      fuzzyForAllHolds params₁
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p)) :
    fuzzyForAllHolds params₂
      (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyForAllHolds_of_lowerPCL_sameEpsilon
    params₁ params₂
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hε hPCL hAll

/-- The finite-domain QFM existential score is monotone under HOL predicate
inheritance, using the existing first-order finite/QFM monotonicity theorem. -/
theorem predicateFuzzyExistsScore_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q) :
    fuzzyExistsScore params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ≤
      fuzzyExistsScore params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ q) := by
  exact
    fuzzyExistsScore_mono_of_pointwise
      params
      (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
      (predicateCrispProfile (Base := Base) (Const := Const) M σ q)
      (predicateCrispProfile_mono_of_inherits
        (Base := Base) (Const := Const) M σ p q hInh)
      (predicateCrispProfile_le_one
        (Base := Base) (Const := Const) M σ q)

/-- Increasing QFM tolerance can only increase the HOL-predicate existential
score, again reusing the finite Chapter-11 theorem. -/
theorem predicateFuzzyExistsScore_mono_of_epsilon_le
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params₁ params₂ : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε : params₁.ε ≤ params₂.ε) :
    fuzzyExistsScore params₁
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ≤
      fuzzyExistsScore params₂
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyExistsScore_mono_of_epsilon_le
    params₁ params₂
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hε

/-- Widening the QFM interval preserves HOL-predicate fuzzy interval
acceptance. -/
theorem predicateFuzzyIntervalHolds_of_wider_bounds
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params₁ params₂ : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε : params₁.ε = params₂.ε)
    (hL : params₂.LPC ≤ params₁.LPC)
    (hU : params₁.UPC ≤ params₂.UPC)
    (hInt :
      fuzzyIntervalHolds params₁
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p)) :
    fuzzyIntervalHolds params₂
      (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyIntervalHolds_of_wider_bounds
    params₁ params₂
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hε hL hU hInt

/-- At the strict finite-QFM endpoint `ε = 0`, `PCL = 1`, HOL-predicate
fuzzy `ForAll` is exactly HOL universal predicate truth. -/
theorem predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Nonempty (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1) :
    fuzzyForAllHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) := by
  rw [crispForAll_endpoint_iff_allEqOne
    (U := PredicateObject (Base := Base) (Const := Const) M σ)
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hε0 hPCL1]
  rw [models_predicateForAllFormula_iff]
  constructor
  · intro h x
    exact
      (predicateCrispProfile_eq_one_iff
        (Base := Base) (Const := Const) M σ p x).1 (h x)
  · intro h x
    exact
      (predicateCrispProfile_eq_one_iff
        (Base := Base) (Const := Const) M σ p x).2 (h x)

/-- On a finite nonempty domain, zero witness fraction means the predicate has
no witnesses. This localizes the counting fact needed to interpret the QFM
`ThereExists` endpoint without changing the first-order QFM API. -/
theorem witnessFraction_eq_zero_iff_forall_not
    {U : Type*} [Fintype U] [Nonempty U]
    (pred : U → Prop) [DecidablePred pred] :
    witnessFraction pred = 0 ↔ ∀ u, ¬ pred u := by
  classical
  unfold witnessFraction
  have hcard_ne : Fintype.card U ≠ 0 := Fintype.card_ne_zero
  simp [hcard_ne, witnessCount]
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h u hp
    exact h.false ⟨u, hp⟩
  · intro h
    exact ⟨fun x => h x.1 x.2⟩

/-- At zero tolerance, a crisp HOL-induced profile is near-zero exactly when
the underlying HOL predicate does not hold at the admissible object. -/
theorem nearZero_predicateCrispProfile_iff_not_holds
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε0 : params.ε = 0)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    nearZero params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p x) ↔
      ¬ predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  classical
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [nearZero, predicateCrispProfile, hx, hε0]
  · simp [nearZero, predicateCrispProfile, hx, hε0]

/-- At zero tolerance, zero near-zero mass of the HOL-induced crisp profile is
exactly HOL universal predicate truth.

This is the counting fact that keeps the QFM `ThereExists` endpoint honest: at
maximal threshold it becomes an all-nonzero condition, not ordinary existential
truth. -/
theorem predicateNearZeroFraction_eq_zero_iff_models_predicateForAllFormula_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Nonempty (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε0 : params.ε = 0) :
    nearZeroFraction params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) = 0 ↔
      HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) := by
  unfold nearZeroFraction
  rw [witnessFraction_eq_zero_iff_forall_not]
  rw [models_predicateForAllFormula_iff]
  constructor
  · intro h x
    by_contra hx
    exact h x ((nearZero_predicateCrispProfile_iff_not_holds
      (Base := Base) (Const := Const) M σ params p hε0 x).2 hx)
  · intro h x hxzero
    exact ((nearZero_predicateCrispProfile_iff_not_holds
      (Base := Base) (Const := Const) M σ params p hε0 x).1 hxzero) (h x)

/-- At `PCL = 1`, the finite-QFM `ThereExists` acceptance predicate is the
zero-near-zero condition for the HOL-induced profile. This is a QFM endpoint
fact, distinct from logical existential truth. -/
theorem predicateFuzzyThereExistsHolds_iff_nearZeroFraction_eq_zero_of_PCL_eq_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hPCL1 : params.PCL = 1) :
    fuzzyThereExistsHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      nearZeroFraction params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) = 0 :=
  fuzzyThereExistsHolds_iff_nearZeroFraction_eq_zero_of_PCL_eq_one
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    hPCL1

/-- At the strict finite-QFM endpoint `ε = 0`, `PCL = 1`, the QFM
`ThereExists` acceptance predicate is again HOL universal predicate truth.

The name deliberately says `ForAllFormula`: this is not logical existential
truth, but the maximal-threshold all-nonzero reading of the PLN-2008 QFM
existential-style check. -/
theorem predicateFuzzyThereExistsHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Nonempty (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1) :
    fuzzyThereExistsHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) := by
  rw [predicateFuzzyThereExistsHolds_iff_nearZeroFraction_eq_zero_of_PCL_eq_one
    (Base := Base) (Const := Const) M σ params p hPCL1]
  exact
    predicateNearZeroFraction_eq_zero_iff_models_predicateForAllFormula_of_epsilon_zero
      (Base := Base) (Const := Const) M σ params p hε0

/-! ## Counting reduction into arbitrary-domain fuzzy quantifiers -/

/-- The HOL-induced crisp finite profile, promoted into the arbitrary-domain
fuzzy-profile interface. This is the compatibility point between the finite
PLN-2008 QFM bundle and the broader WM-calc fuzzy quantifier semantics. -/
noncomputable def predicateCrispProfileInf
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    FuzzyProfile (PredicateObject (Base := Base) (Const := Const) M σ) :=
  boundedProfileFinToInf
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

@[simp] theorem predicateCrispProfileInf_apply
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    ((predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) x : ℝ) =
      predicateCrispProfile (Base := Base) (Const := Const) M σ p x := by
  simp [predicateCrispProfileInf]

/-- The HOL model-theoretic extension of a unary predicate over the admissible
objects of a pointed Henkin model. This is the support that arbitrary
capacities see when they consume a HOL-induced crisp QFM profile. -/
def predicateExtension
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    Set (PredicateObject (Base := Base) (Const := Const) M σ) :=
  {x | predicateHoldsAt (Base := Base) (Const := Const) M σ p x}

/-- Arbitrary finite cardinality thresholds for a HOL predicate extension are
equivalent to arbitrary finite witness sets of admissible objects satisfying
the predicate.  This is the generic semantic spine behind the constructed
`∃`, `at least two`, and `at least three` HOL counting sentences below. -/
theorem predicateExtension_ncard_ge_iff_exists_witnessSet
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : Nat) :
    k ≤ (predicateExtension (Base := Base) (Const := Const) M σ p).ncard ↔
      ∃ W : Set (PredicateObject (Base := Base) (Const := Const) M σ),
        W.ncard = k ∧
          ∀ x ∈ W, predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  constructor
  · intro hk
    rcases Set.exists_subset_card_eq hk with ⟨W, hWsub, hWcard⟩
    refine ⟨W, hWcard, ?_⟩
    intro x hx
    exact hWsub hx
  · rintro ⟨W, hWcard, hW⟩
    rw [← hWcard]
    exact Set.ncard_le_ncard
      (by
        intro x hx
        exact hW x hx)
      (Set.toFinite _)

/-- Arbitrary finite cardinality thresholds for the complement of a HOL
predicate extension are equivalent to arbitrary finite non-witness sets. -/
theorem predicateExtension_compl_ncard_ge_iff_exists_nonwitnessSet
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : Nat) :
    k ≤ (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ.ncard ↔
      ∃ W : Set (PredicateObject (Base := Base) (Const := Const) M σ),
        W.ncard = k ∧
          ∀ x ∈ W, ¬ predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  constructor
  · intro hk
    rcases Set.exists_subset_card_eq hk with ⟨W, hWsub, hWcard⟩
    refine ⟨W, hWcard, ?_⟩
    intro x hx
    exact hWsub hx
  · rintro ⟨W, hWcard, hW⟩
    rw [← hWcard]
    exact Set.ncard_le_ncard
      (by
        intro x hx
        exact hW x hx)
      (Set.toFinite _)

/-- Right-associated finite conjunction over a `Fin n`-indexed formula
family.  The empty conjunction is truth. -/
def finiteConjunctionFormula {Γ : Ctx Base} : {n : Nat} →
    (Fin n → Formula Const Γ) → Formula Const Γ
  | 0, _ => .top
  | n + 1, f => .and (f 0) (finiteConjunctionFormula (fun i : Fin n => f i.succ))

/-- Constants absent from every member of a finite family remain absent from
its finite conjunction. -/
theorem noConstOccurrence_finiteConjunctionFormula
    {τ : Ty Base} {c : Const τ} {Γ : Ctx Base} {n : Nat}
    (f : Fin n → Formula Const Γ)
    (hf : ∀ i, NoConstOccurrence c (f i)) :
    NoConstOccurrence c (finiteConjunctionFormula f) := by
  induction n with
  | zero => exact NoConstOccurrence.top
  | succ n ih =>
      exact NoConstOccurrence.and (hf 0)
        (ih (fun i : Fin n => f i.succ) (fun i => hf i.succ))

/-- A closed base-type unary predicate weakened into a repeated base-variable
context.  The `n` variables are precisely the candidate witnesses used by
`predicateAtLeastNBaseFormula`. -/
def repeatedBasePredicate
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    (n : Nat) → Term Const (List.replicate n (.base b)) ((.base b) ⇒ propTy)
  | 0 => p
  | n + 1 =>
      weaken (Base := Base) (Const := Const) (σ := .base b)
        (repeatedBasePredicate b p n)

/-- Constants absent from a closed predicate remain absent after weakening it
into any repeated base-variable context. -/
theorem noConstOccurrence_repeatedBasePredicate
    {τ : Ty Base} {c : Const τ}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (hpc : NoConstOccurrence c p) :
    ∀ n, NoConstOccurrence c
      (repeatedBasePredicate (Base := Base) (Const := Const) b p n)
  | 0 => hpc
  | n + 1 =>
      noConstOccurrence_rename
        (Rename.weaken (Base := Base) (Γ := List.replicate n (.base b))
          (σ := .base b))
        (repeatedBasePredicate (Base := Base) (Const := Const) b p n)
        (noConstOccurrence_repeatedBasePredicate b p hpc n)

/-- Conjunction saying that all `n` candidate base witnesses satisfy the
predicate. -/
def predicateWitnessConjunctionBaseFormula
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    (n : Nat) → Formula Const (List.replicate n (.base b))
  | 0 => .top
  | n + 1 =>
      .and
        (.app (repeatedBasePredicate (Base := Base) (Const := Const) b p (n + 1))
          (.var .vz))
        (weaken (Base := Base) (Const := Const) (σ := .base b)
          (predicateWitnessConjunctionBaseFormula b p n))

/-- Constants absent from the predicate remain absent from the finite witness
conjunction. -/
theorem noConstOccurrence_predicateWitnessConjunctionBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (hpc : NoConstOccurrence c p) :
    ∀ n, NoConstOccurrence c
      (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n)
  | 0 => NoConstOccurrence.top
  | n + 1 => by
      refine NoConstOccurrence.and ?_ ?_
      · exact NoConstOccurrence.app
          (noConstOccurrence_repeatedBasePredicate b p hpc (n + 1))
          NoConstOccurrence.var
      · exact noConstOccurrence_rename
          (Rename.weaken (Base := Base) (Γ := List.replicate n (.base b))
            (σ := .base b))
          (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n)
          (noConstOccurrence_predicateWitnessConjunctionBaseFormula b p hpc n)

/-- The newest candidate base witness is distinct from every previous
candidate in the repeated base-variable context. -/
def newestDistinctFromPreviousBaseFormula
    (b : Base) (n : Nat) :
    Formula Const ((.base b) :: List.replicate n (.base b)) :=
  finiteConjunctionFormula (fun i : Fin n =>
    .not (.eq (.var .vz)
      (.var (.vs (Var.ofFinRepeat (.base b) n i)))))

/-- The distinctness-only formula contains no constants. -/
theorem noConstOccurrence_newestDistinctFromPreviousBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base) (n : Nat) :
    NoConstOccurrence c
      (newestDistinctFromPreviousBaseFormula (Base := Base) (Const := Const) b n) := by
  exact noConstOccurrence_finiteConjunctionFormula _ (fun _ =>
    NoConstOccurrence.not (NoConstOccurrence.eq NoConstOccurrence.var NoConstOccurrence.var))

/-- Pairwise distinctness for all candidate base witnesses in a repeated
base-variable context. -/
def pairwiseDistinctBaseFormula
    (b : Base) : (n : Nat) → Formula Const (List.replicate n (.base b))
  | 0 => .top
  | n + 1 =>
      .and (newestDistinctFromPreviousBaseFormula (Base := Base) (Const := Const) b n)
        (weaken (Base := Base) (Const := Const) (σ := .base b)
          (pairwiseDistinctBaseFormula b n))

/-- Pairwise distinctness formulas contain no constants. -/
theorem noConstOccurrence_pairwiseDistinctBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base) :
    ∀ n, NoConstOccurrence c
      (pairwiseDistinctBaseFormula (Base := Base) (Const := Const) b n)
  | 0 => NoConstOccurrence.top
  | n + 1 => by
      refine NoConstOccurrence.and ?_ ?_
      · exact noConstOccurrence_newestDistinctFromPreviousBaseFormula b n
      · exact noConstOccurrence_rename
          (Rename.weaken (Base := Base) (Γ := List.replicate n (.base b))
            (σ := .base b))
          (pairwiseDistinctBaseFormula (Base := Base) (Const := Const) b n)
          (noConstOccurrence_pairwiseDistinctBaseFormula b n)

/-- Close a formula over `n` repeated base variables by existentially
quantifying all of them. -/
def closeExistsBaseFormula
    (b : Base) :
    (n : Nat) → Formula Const (List.replicate n (.base b)) → ClosedFormula Const
  | 0, φ => φ
  | n + 1, φ => closeExistsBaseFormula b n (.ex φ)

/-- Closing by repeated existential quantification preserves absence of
constants. -/
theorem noConstOccurrence_closeExistsBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base) :
    ∀ (n : Nat) (φ : Formula Const (List.replicate n (.base b))),
      NoConstOccurrence c φ →
        NoConstOccurrence c
          (closeExistsBaseFormula (Base := Base) (Const := Const) b n φ)
  | 0, _, hφ => hφ
  | n + 1, φ, hφ =>
      noConstOccurrence_closeExistsBaseFormula b n (.ex φ)
        (NoConstOccurrence.ex hφ)

/-- The uniform closed HOL sentence asserting that at least `k` distinct base
objects satisfy a unary HOL predicate.

The semantic cardinality theorem for this uniform syntax is intentionally a
separate layer: this definition provides the reusable closed formula and the
param-freeness theorem below, while concrete endpoint tightness still requires
a discharged `represents_ge` bridge. -/
def predicateAtLeastNBaseFormula
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (k : Nat) : ClosedFormula Const :=
  closeExistsBaseFormula b k
    (.and
      (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p k)
      (pairwiseDistinctBaseFormula (Base := Base) (Const := Const) b k))

/-- Constants absent from the predicate remain absent from the uniform
`at least k base witnesses` sentence. -/
theorem noConstOccurrence_predicateAtLeastNBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (hpc : NoConstOccurrence c p)
    (k : Nat) :
    NoConstOccurrence c
      (predicateAtLeastNBaseFormula (Base := Base) (Const := Const) b p k) := by
  exact noConstOccurrence_closeExistsBaseFormula b k _
    (NoConstOccurrence.and
      (noConstOccurrence_predicateWitnessConjunctionBaseFormula b p hpc k)
      (noConstOccurrence_pairwiseDistinctBaseFormula b k))

/-- Valuation generated by a finite tuple of base-type admissible objects.
Index `0` is the newest de Bruijn variable, matching the syntax generated by
`predicateAtLeastNBaseFormula`. -/
def repeatedBaseValuation
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base) : {n : Nat} →
    (Fin n → PredicateObject (Base := Base) (Const := Const) M (.base b)) →
      HenkinModel.Valuation M (List.replicate n (.base b))
  | 0, _ => closedValuation M
  | n + 1, xs =>
      HenkinModel.extend M (repeatedBaseValuation M b (fun i : Fin n => xs i.succ))
        (xs 0).1

/-- Looking up `Fin`-indexed repeated variables in the repeated-base valuation
returns the corresponding tuple element. -/
theorem repeatedBaseValuation_ofFinRepeat
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base) : ∀ {n : Nat}
    (xs : Fin n → PredicateObject (Base := Base) (Const := Const) M (.base b))
    (i : Fin n),
      repeatedBaseValuation (Base := Base) (Const := Const) M b xs
        (Var.ofFinRepeat (.base b) n i) = (xs i).1 := by
  intro n
  induction n with
  | zero =>
      intro xs i
      exact Fin.elim0 i
  | succ n ih =>
      intro xs i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change repeatedBaseValuation (Base := Base) (Const := Const) M b
              (fun j : Fin n => xs j.succ)
              (Var.ofFinRepeat (.base b) n i) = (xs i.succ).1
          exact ih (fun j : Fin n => xs j.succ) i

/-- Weakening a closed base predicate into a repeated base-variable context
does not change its denotation under the repeated-base valuation. -/
theorem denote_repeatedBasePredicate_eq_closed
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    ∀ {n : Nat}
    (xs : Fin n → PredicateObject (Base := Base) (Const := Const) M (.base b)),
      HenkinModel.denote M
        (repeatedBasePredicate (Base := Base) (Const := Const) b p n)
        (repeatedBaseValuation (Base := Base) (Const := Const) M b xs) =
      HenkinModel.denote M p (closedValuation M) := by
  intro n
  induction n with
  | zero =>
      intro xs
      rfl
  | succ n ih =>
      intro xs
      change HenkinModel.denote M
          (weaken (Base := Base) (Const := Const) (σ := .base b)
            (repeatedBasePredicate (Base := Base) (Const := Const) b p n))
          (HenkinModel.extend M
            (repeatedBaseValuation (Base := Base) (Const := Const) M b
              (fun i : Fin n => xs i.succ)) (xs 0).1) =
        HenkinModel.denote M p (closedValuation M)
      rw [Mettapedia.Logic.HOL.Soundness.denote_weaken]
      exact ih (fun i : Fin n => xs i.succ)

/-- Applying the repeated-context predicate to the `i`th repeated variable is
equivalent to ordinary HOL predicate satisfaction at the `i`th tuple element. -/
theorem denote_repeatedBasePredicate_app_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    {n : Nat}
    (xs : Fin n → PredicateObject (Base := Base) (Const := Const) M (.base b))
    (i : Fin n) :
    (HenkinModel.denote M
      (.app (repeatedBasePredicate (Base := Base) (Const := Const) b p n)
        (.var (Var.ofFinRepeat (.base b) n i)))
      (repeatedBaseValuation (Base := Base) (Const := Const) M b xs)).down ↔
      predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p (xs i) := by
  unfold predicateHoldsAt
  change ((HenkinModel.denote M
      (repeatedBasePredicate (Base := Base) (Const := Const) b p n)
      (repeatedBaseValuation (Base := Base) (Const := Const) M b xs))
        (repeatedBaseValuation (Base := Base) (Const := Const) M b xs
          (Var.ofFinRepeat (.base b) n i))).down ↔
      ((HenkinModel.denote M
        (weaken (Base := Base) (Const := Const) (σ := .base b) p)
        (HenkinModel.extend M (closedValuation M) (xs i).1))
          (HenkinModel.extend M (closedValuation M) (xs i).1 Var.vz)).down
  rw [denote_repeatedBasePredicate_eq_closed]
  rw [repeatedBaseValuation_ofFinRepeat]
  rw [Mettapedia.Logic.HOL.Soundness.denote_weaken]
  rfl

/-- Weakening the witness conjunction into one more repeated variable drops
back to the tail tuple under the repeated-base valuation. -/
theorem denote_weaken_predicateWitnessConjunctionBaseFormula_tail
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    {n : Nat}
    (xs : Fin (n + 1) → PredicateObject (Base := Base) (Const := Const) M (.base b)) :
    HenkinModel.denote M
      (weaken (Base := Base) (Const := Const) (σ := .base b)
        (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n))
      (repeatedBaseValuation (Base := Base) (Const := Const) M b xs) =
    HenkinModel.denote M
      (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n)
      (repeatedBaseValuation (Base := Base) (Const := Const) M b
        (fun i : Fin n => xs i.succ)) := by
  change HenkinModel.denote M
      (weaken (Base := Base) (Const := Const) (σ := .base b)
        (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n))
      (HenkinModel.extend M
        (repeatedBaseValuation (Base := Base) (Const := Const) M b
          (fun i : Fin n => xs i.succ)) (xs 0).1) =
    HenkinModel.denote M
      (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n)
      (repeatedBaseValuation (Base := Base) (Const := Const) M b
        (fun i : Fin n => xs i.succ))
  rw [Mettapedia.Logic.HOL.Soundness.denote_weaken]

/-- The finite witness conjunction generated by `predicateAtLeastNBaseFormula`
is true exactly when every tuple entry satisfies the HOL predicate. -/
theorem denote_predicateWitnessConjunctionBaseFormula_iff_forall
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    ∀ {n : Nat}
    (xs : Fin n → PredicateObject (Base := Base) (Const := Const) M (.base b)),
    (HenkinModel.denote M
      (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n)
      (repeatedBaseValuation (Base := Base) (Const := Const) M b xs)).down ↔
      ∀ i : Fin n,
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p (xs i) := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [predicateWitnessConjunctionBaseFormula]
  | succ n ih =>
      intro xs
      change ((HenkinModel.denote M
        (.app (repeatedBasePredicate (Base := Base) (Const := Const) b p (n + 1))
          (.var (Var.ofFinRepeat (.base b) (n + 1) 0)))
        (repeatedBaseValuation (Base := Base) (Const := Const) M b xs)).down ∧
        (HenkinModel.denote M
          (weaken (Base := Base) (Const := Const) (σ := .base b)
            (predicateWitnessConjunctionBaseFormula (Base := Base) (Const := Const) b p n))
          (repeatedBaseValuation (Base := Base) (Const := Const) M b xs)).down) ↔
          ∀ i : Fin (n + 1),
            predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p (xs i)
      rw [denote_weaken_predicateWitnessConjunctionBaseFormula_tail]
      constructor
      · rintro ⟨h0, htail⟩ i
        cases i using Fin.cases with
        | zero =>
            exact (denote_repeatedBasePredicate_app_iff
              (Base := Base) (Const := Const) M b p xs 0).mp h0
        | succ i =>
            exact (ih (fun j : Fin n => xs j.succ)).mp htail i
      · intro h
        constructor
        · exact (denote_repeatedBasePredicate_app_iff
            (Base := Base) (Const := Const) M b p xs 0).mpr (h 0)
        · exact (ih (fun j : Fin n => xs j.succ)).mpr (fun i => h i.succ)

/-- Constants absent from the predicate remain absent from the existential
witness sentence. -/
theorem noConstOccurrence_predicateExistsFormula
    {τ : Ty Base} {c : Const τ}
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpc : NoConstOccurrence c p) :
    NoConstOccurrence c
      (predicateExistsFormula (Base := Base) (Const := Const) σ p) := by
  exact NoConstOccurrence.ex
    (NoConstOccurrence.app
      (noConstOccurrence_rename
        (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) p hpc)
      NoConstOccurrence.var)

/-- The HOL sentence `∃ x, p x` is satisfied exactly when the predicate
extension has at least one element. -/
theorem models_predicateExistsFormula_iff_one_le_ncard_extension
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M (predicateExistsFormula (Base := Base) (Const := Const) σ p) ↔
      1 ≤ (predicateExtension (Base := Base) (Const := Const) M σ p).ncard := by
  rw [models_predicateExistsFormula_iff]
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    have hExtNonempty :
        (predicateExtension (Base := Base) (Const := Const) M σ p).Nonempty :=
      ⟨x, by simpa [predicateExtension] using hx⟩
    have hExtPos :
        0 < (predicateExtension (Base := Base) (Const := Const) M σ p).ncard := by
      exact (Set.ncard_pos).2 hExtNonempty
    omega
  · intro h
    have hExtPos :
        0 < (predicateExtension (Base := Base) (Const := Const) M σ p).ncard := by
      omega
    rcases (Set.ncard_pos).1 hExtPos with ⟨x, hx⟩
    exact ⟨x, by simpa [predicateExtension] using hx⟩

/-- The closed HOL sentence expressing `∃ x, ¬ p x`.  This is the direct
formula-level witness for a nonempty complement of the HOL predicate
extension. -/
def predicateExistsNotFormula
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    ClosedFormula Const :=
  .ex (.not (.app (weaken (Base := Base) (σ := σ) p) (.var .vz)))

/-- Constants absent from the predicate remain absent from the existential
non-witness sentence. -/
theorem noConstOccurrence_predicateExistsNotFormula
    {τ : Ty Base} {c : Const τ}
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpc : NoConstOccurrence c p) :
    NoConstOccurrence c
      (predicateExistsNotFormula (Base := Base) (Const := Const) σ p) := by
  exact NoConstOccurrence.ex
    (NoConstOccurrence.not
      (NoConstOccurrence.app
        (noConstOccurrence_rename
          (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) p hpc)
        NoConstOccurrence.var))

/-- The HOL sentence `∃ x, ¬ p x` is satisfied exactly when there is an
admissible object outside the predicate extension. -/
theorem models_predicateExistsNotFormula_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M (predicateExistsNotFormula (Base := Base) (Const := Const) σ p) ↔
      ∃ x : PredicateObject (Base := Base) (Const := Const) M σ,
        ¬ predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  constructor
  · intro h
    have hex :
        ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
          ¬ (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      change ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
          ¬ (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down at h
      exact h
    rcases hex with ⟨y, hy, hp⟩
    exact ⟨⟨y, hy⟩, by
      intro hholds
      exact hp (by simpa [predicateHoldsAt, closedValuation] using hholds)⟩
  · intro h
    rcases h with ⟨x, hp⟩
    have hex :
        ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
          ¬ (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down :=
      ⟨x.1, x.2, by
        intro hden
        exact hp (by simpa [predicateHoldsAt, closedValuation] using hden)⟩
    change HenkinModel.models M (predicateExistsNotFormula (Base := Base) (Const := Const) σ p)
    exact hex

/-- In a finite carrier of exact cardinality `N`, the non-witness sentence
represents the upper-cardinality event `ncard(ext p) + 1 ≤ N`. -/
theorem models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (N : Nat)
    (hCard :
      Fintype.card (PredicateObject (Base := Base) (Const := Const) M σ) = N) :
    HenkinModel.models M (predicateExistsNotFormula (Base := Base) (Const := Const) σ p) ↔
      (predicateExtension (Base := Base) (Const := Const) M σ p).ncard + 1 ≤ N := by
  rw [models_predicateExistsNotFormula_iff]
  have hNatCard :
      Nat.card (PredicateObject (Base := Base) (Const := Const) M σ) = N := by
    rw [Nat.card_eq_fintype_card, hCard]
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    have hComplNonempty :
        ((predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ).Nonempty :=
      ⟨x, by simpa [predicateExtension] using hx⟩
    have hComplPos :
        0 < ((predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ).ncard := by
      exact (Set.ncard_pos).2 hComplNonempty
    rw [Set.ncard_compl, hNatCard] at hComplPos
    exact Nat.add_one_le_iff.mpr (Nat.lt_of_sub_pos hComplPos)
  · intro h
    by_contra hNo
    have hAll :
        ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
          x ∈ predicateExtension (Base := Base) (Const := Const) M σ p := by
      intro x
      by_contra hx
      exact hNo ⟨x, by simpa [predicateExtension] using hx⟩
    have hExtEq :
        predicateExtension (Base := Base) (Const := Const) M σ p = Set.univ := by
      ext x
      simp [hAll x]
    have hncard :
        (predicateExtension (Base := Base) (Const := Const) M σ p).ncard = N := by
      rw [hExtEq, Set.ncard_univ, hNatCard]
    omega

/-- The closed base-type HOL sentence expressing that at least two distinct
objects satisfy a unary predicate.

The base-type restriction is intentional: at higher HOL types, equality is the
model's extensional equivalence relation, while the counting support below is a
set of admissible objects.  For base objects, extensional equality is literal
object equality, so the formula exactly represents a cardinality-`2` event. -/
def predicateAtLeastTwoBaseFormula
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    ClosedFormula Const :=
  .ex (.ex
    (.and
      (.and
        (.app
          (weaken (Base := Base) (Const := Const) (σ := .base b)
            (weaken (Base := Base) (Const := Const) (σ := .base b) p))
          (.var (.vs .vz)))
        (.app
          (weaken (Base := Base) (Const := Const) (σ := .base b)
            (weaken (Base := Base) (Const := Const) (σ := .base b) p))
          (.var .vz)))
      (.not (.eq (.var (.vs .vz)) (.var .vz)))))

/-- Constants absent from the predicate remain absent from the base-type
`at least two witnesses` sentence. -/
theorem noConstOccurrence_predicateAtLeastTwoBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (hpc : NoConstOccurrence c p) :
    NoConstOccurrence c
      (predicateAtLeastTwoBaseFormula (Base := Base) (Const := Const) b p) := by
  refine NoConstOccurrence.ex ?_
  refine NoConstOccurrence.ex ?_
  refine NoConstOccurrence.and ?_ ?_
  · refine NoConstOccurrence.and ?_ ?_
    · exact NoConstOccurrence.app
        (noConstOccurrence_rename
          (Rename.weaken (Base := Base) (Γ := [.base b]) (σ := .base b))
          (weaken (Base := Base) (Const := Const) (σ := .base b) p)
          (noConstOccurrence_rename
            (Rename.weaken (Base := Base) (Γ := []) (σ := .base b)) p hpc))
        NoConstOccurrence.var
    · exact NoConstOccurrence.app
        (noConstOccurrence_rename
          (Rename.weaken (Base := Base) (Γ := [.base b]) (σ := .base b))
          (weaken (Base := Base) (Const := Const) (σ := .base b) p)
          (noConstOccurrence_rename
            (Rename.weaken (Base := Base) (Γ := []) (σ := .base b)) p hpc))
        NoConstOccurrence.var
  · exact NoConstOccurrence.not
      (NoConstOccurrence.eq NoConstOccurrence.var NoConstOccurrence.var)

/-- The base-type `at least two witnesses` sentence is satisfied exactly when
there are two distinct admissible base objects satisfying the predicate. -/
theorem models_predicateAtLeastTwoBaseFormula_iff_exists_distinct
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    HenkinModel.models M (predicateAtLeastTwoBaseFormula (Base := Base) (Const := Const) b p) ↔
      ∃ x y : PredicateObject (Base := Base) (Const := Const) M (.base b),
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p x ∧
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p y ∧ x ≠ y := by
  simp only [predicateAtLeastTwoBaseFormula, HenkinModel.models, PreModel.models,
    PreModel.denote, PreModel.Eqv]
  constructor
  · intro h
    rcases h with ⟨x, hx, y, hy, ⟨hpx, hpy⟩, hne⟩
    have hOuterEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b) p))
            (.var (.vs .vz)))
          (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x) y) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) x) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) x = M.denote p (closedValuation M) x
      rfl
    have hInnerEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b) p))
            (.var .vz))
          (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x) y) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) y = M.denote p (closedValuation M) y
      rfl
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_, ?_, ?_⟩
    · unfold predicateHoldsAt
      exact (congrArg ULift.down hOuterEq).mp hpx
    · unfold predicateHoldsAt
      exact (congrArg ULift.down hInnerEq).mp hpy
    · intro hxy
      exact hne (congrArg Subtype.val hxy)
  · intro h
    rcases h with ⟨x, y, hpx, hpy, hne⟩
    have hOuterEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b) p))
            (.var (.vs .vz)))
          (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x.1) y.1) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) x.1) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) x.1 = M.denote p (closedValuation M) x.1
      rfl
    have hInnerEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b) p))
            (.var .vz))
          (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x.1) y.1) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y.1) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) y.1 = M.denote p (closedValuation M) y.1
      rfl
    refine ⟨x.1, x.2, y.1, y.2, ⟨?_, ?_⟩, ?_⟩
    · unfold predicateHoldsAt at hpx
      exact (congrArg ULift.down hOuterEq).mpr hpx
    · unfold predicateHoldsAt at hpy
      exact (congrArg ULift.down hInnerEq).mpr hpy
    · intro hxy
      exact hne (Subtype.ext hxy)

/-- On base types, the `at least two witnesses` sentence represents the
cardinality-threshold event `2 ≤ ncard (ext p)`. -/
theorem models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M (.base b))]
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    HenkinModel.models M (predicateAtLeastTwoBaseFormula (Base := Base) (Const := Const) b p) ↔
      2 ≤ (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
  rw [models_predicateAtLeastTwoBaseFormula_iff_exists_distinct]
  constructor
  · intro h
    rcases h with ⟨x, y, hpx, hpy, hne⟩
    have hOne :
        1 < (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨x, by simpa [predicateExtension] using hpx, y,
        by simpa [predicateExtension] using hpy, hne⟩
    omega
  · intro h
    have hOne :
        1 < (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
      omega
    rcases (Set.one_lt_ncard
        (s := predicateExtension (Base := Base) (Const := Const) M (.base b) p)).mp hOne with
      ⟨x, hx, y, hy, hne⟩
    exact ⟨x, y, by simpa [predicateExtension] using hx,
      by simpa [predicateExtension] using hy, hne⟩

/-- The closed HOL sentence expressing that at least three distinct base
objects satisfy a unary HOL predicate.

As with `predicateAtLeastTwoBaseFormula`, this is restricted to base types:
base equality is literal object equality, so the formula represents a concrete
cardinality threshold for the admissible-object extension. -/
def predicateAtLeastThreeBaseFormula
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    ClosedFormula Const :=
  .ex (.ex (.ex
    (.and
      (.and
        (.and
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs (.vs .vz))))
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs .vz))))
        (.app
          (weaken (Base := Base) (Const := Const) (σ := .base b)
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
          (.var .vz)))
      (.and
        (.and
          (.not (.eq (.var (.vs (.vs .vz))) (.var (.vs .vz))))
          (.not (.eq (.var (.vs (.vs .vz))) (.var .vz))))
        (.not (.eq (.var (.vs .vz)) (.var .vz)))))))

/-- Constants absent from the predicate remain absent from the base-type
`at least three witnesses` sentence. -/
theorem noConstOccurrence_predicateAtLeastThreeBaseFormula
    {τ : Ty Base} {c : Const τ}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b))
    (hpc : NoConstOccurrence c p) :
    NoConstOccurrence c
      (predicateAtLeastThreeBaseFormula (Base := Base) (Const := Const) b p) := by
  have hp1 : NoConstOccurrence c
      (weaken (Base := Base) (Const := Const) (σ := .base b) p) :=
    noConstOccurrence_rename
      (Rename.weaken (Base := Base) (Γ := []) (σ := .base b)) p hpc
  have hp2 : NoConstOccurrence c
      (weaken (Base := Base) (Const := Const) (σ := .base b)
        (weaken (Base := Base) (Const := Const) (σ := .base b) p)) :=
    noConstOccurrence_rename
      (Rename.weaken (Base := Base) (Γ := [.base b]) (σ := .base b))
      (weaken (Base := Base) (Const := Const) (σ := .base b) p) hp1
  have hp3 : NoConstOccurrence c
      (weaken (Base := Base) (Const := Const) (σ := .base b)
        (weaken (Base := Base) (Const := Const) (σ := .base b)
          (weaken (Base := Base) (Const := Const) (σ := .base b) p))) :=
    noConstOccurrence_rename
      (Rename.weaken (Base := Base) (Γ := [.base b, .base b]) (σ := .base b))
      (weaken (Base := Base) (Const := Const) (σ := .base b)
        (weaken (Base := Base) (Const := Const) (σ := .base b) p)) hp2
  refine NoConstOccurrence.ex ?_
  refine NoConstOccurrence.ex ?_
  refine NoConstOccurrence.ex ?_
  refine NoConstOccurrence.and ?_ ?_
  · refine NoConstOccurrence.and ?_ ?_
    · refine NoConstOccurrence.and ?_ ?_
      · exact NoConstOccurrence.app hp3 NoConstOccurrence.var
      · exact NoConstOccurrence.app hp3 NoConstOccurrence.var
    · exact NoConstOccurrence.app hp3 NoConstOccurrence.var
  · refine NoConstOccurrence.and ?_ ?_
    · refine NoConstOccurrence.and ?_ ?_
      · exact NoConstOccurrence.not
          (NoConstOccurrence.eq NoConstOccurrence.var NoConstOccurrence.var)
      · exact NoConstOccurrence.not
          (NoConstOccurrence.eq NoConstOccurrence.var NoConstOccurrence.var)
    · exact NoConstOccurrence.not
        (NoConstOccurrence.eq NoConstOccurrence.var NoConstOccurrence.var)

/-- The base-type `at least three witnesses` sentence is satisfied exactly
when three pairwise distinct admissible base objects satisfy the predicate. -/
theorem models_predicateAtLeastThreeBaseFormula_iff_exists_distinct
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    HenkinModel.models M (predicateAtLeastThreeBaseFormula (Base := Base) (Const := Const) b p) ↔
      ∃ x y z : PredicateObject (Base := Base) (Const := Const) M (.base b),
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p x ∧
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p y ∧
        predicateHoldsAt (Base := Base) (Const := Const) M (.base b) p z ∧
          x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  simp only [predicateAtLeastThreeBaseFormula, HenkinModel.models, PreModel.models,
    PreModel.denote, PreModel.Eqv]
  constructor
  · intro h
    rcases h with
      ⟨x, hx, y, hy, z, hz, ⟨⟨hpx, hpy⟩, hpz⟩, ⟨⟨hxy, hxz⟩, hyz⟩⟩
    have hOuterEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs (.vs .vz))))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x) y) z) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) x) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) x = M.denote p (closedValuation M) x
      rfl
    have hMiddleEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs .vz)))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x) y) z) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) y = M.denote p (closedValuation M) y
      rfl
    have hInnerEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var .vz))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x) y) z) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) z) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) z = M.denote p (closedValuation M) z
      rfl
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold predicateHoldsAt
      exact (congrArg ULift.down hOuterEq).mp hpx
    · unfold predicateHoldsAt
      exact (congrArg ULift.down hMiddleEq).mp hpy
    · unfold predicateHoldsAt
      exact (congrArg ULift.down hInnerEq).mp hpz
    · intro h
      exact hxy (congrArg Subtype.val h)
    · intro h
      exact hxz (congrArg Subtype.val h)
    · intro h
      exact hyz (congrArg Subtype.val h)
  · intro h
    rcases h with ⟨x, y, z, hpx, hpy, hpz, hxy, hxz, hyz⟩
    have hOuterEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs (.vs .vz))))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x.1) y.1) z.1) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) x.1) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) x.1 = M.denote p (closedValuation M) x.1
      rfl
    have hMiddleEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var (.vs .vz)))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x.1) y.1) z.1) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y.1) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) y.1 = M.denote p (closedValuation M) y.1
      rfl
    have hInnerEq :
        HenkinModel.denote M
          (.app
            (weaken (Base := Base) (Const := Const) (σ := .base b)
              (weaken (Base := Base) (Const := Const) (σ := .base b)
                (weaken (Base := Base) (Const := Const) (σ := .base b) p)))
            (.var .vz))
          (HenkinModel.extend M
            (HenkinModel.extend M (HenkinModel.extend M (closedValuation M) x.1) y.1) z.1) =
        HenkinModel.denote M
          (.app (weaken (Base := Base) (Const := Const) (σ := .base b) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) z.1) := by
      simp [HenkinModel.denote, PreModel.denote,
        Mettapedia.Logic.HOL.Soundness.denote_weaken]
      change M.denote p (closedValuation M) z.1 = M.denote p (closedValuation M) z.1
      rfl
    refine ⟨x.1, x.2, y.1, y.2, z.1, z.2, ?_, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · unfold predicateHoldsAt at hpx
        exact (congrArg ULift.down hOuterEq).mpr hpx
      · unfold predicateHoldsAt at hpy
        exact (congrArg ULift.down hMiddleEq).mpr hpy
      · unfold predicateHoldsAt at hpz
        exact (congrArg ULift.down hInnerEq).mpr hpz
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro h
        exact hxy (Subtype.ext h)
      · intro h
        exact hxz (Subtype.ext h)
      · intro h
        exact hyz (Subtype.ext h)

/-- On base types, the `at least three witnesses` sentence represents the
cardinality-threshold event `3 ≤ ncard (ext p)`. -/
theorem models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
    (M : HenkinModel.{u, v, w} Base Const)
    (b : Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M (.base b))]
    (p : UnaryPredicate (Base := Base) (Const := Const) (.base b)) :
    HenkinModel.models M (predicateAtLeastThreeBaseFormula (Base := Base) (Const := Const) b p) ↔
      3 ≤ (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
  rw [models_predicateAtLeastThreeBaseFormula_iff_exists_distinct]
  constructor
  · intro h
    rcases h with ⟨x, y, z, hpx, hpy, hpz, hxy, hxz, hyz⟩
    have hTwo :
        2 < (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
      rw [Set.two_lt_ncard_iff]
      exact ⟨x, y, z, by simpa [predicateExtension] using hpx,
        by simpa [predicateExtension] using hpy,
        by simpa [predicateExtension] using hpz, hxy, hxz, hyz⟩
    omega
  · intro h
    have hTwo :
        2 < (predicateExtension (Base := Base) (Const := Const) M (.base b) p).ncard := by
      omega
    rcases (Set.two_lt_ncard_iff
        (s := predicateExtension (Base := Base) (Const := Const) M (.base b) p)).mp hTwo with
      ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
    exact ⟨x, y, z, by simpa [predicateExtension] using hx,
      by simpa [predicateExtension] using hy,
      by simpa [predicateExtension] using hz, hxy, hxz, hyz⟩

/-- The arbitrary-domain fuzzy profile induced by a HOL predicate is exactly
the crisp indicator of its Henkin-model extension. -/
theorem predicateCrispProfileInf_eq_crispIndicator_extension
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    predicateCrispProfileInf (Base := Base) (Const := Const) M σ p =
      FuzzyProfile.crispIndicator
        (predicateExtension (Base := Base) (Const := Const) M σ p) := by
  change FuzzyProfile.mk
      (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p).eval =
    FuzzyProfile.mk
      (FuzzyProfile.crispIndicator
        (predicateExtension (Base := Base) (Const := Const) M σ p)).eval
  apply congrArg FuzzyProfile.mk
  funext x
  classical
  apply Subtype.ext
  by_cases hx : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [predicateCrispProfileInf_apply, predicateCrispProfile,
      FuzzyProfile.crispIndicator, predicateExtension, hx]
  · simp [predicateCrispProfileInf_apply, predicateCrispProfile,
      FuzzyProfile.crispIndicator, predicateExtension, hx]

theorem predicateCrispProfileInf_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) :
    predicateCrispProfileInf (Base := Base) (Const := Const) M σ p x ≤
      predicateCrispProfileInf (Base := Base) (Const := Const) M σ q x := by
  change
    predicateCrispProfile (Base := Base) (Const := Const) M σ p x ≤
      predicateCrispProfile (Base := Base) (Const := Const) M σ q x
  exact
    predicateCrispProfile_mono_of_inherits
      (Base := Base) (Const := Const) M σ p q hInh x

theorem predicateCrispProfileInf_eq_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    predicateCrispProfileInf (Base := Base) (Const := Const) M σ p =
      predicateCrispProfileInf (Base := Base) (Const := Const) M σ q := by
  change
    FuzzyProfile.mk
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p).eval =
      FuzzyProfile.mk
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q).eval
  apply congrArg FuzzyProfile.mk
  funext x
  apply Subtype.ext
  simp only [predicateCrispProfileInf_apply]
  exact congrFun
    (predicateCrispProfile_eq_of_pointwiseIff
      (Base := Base) (Const := Const) M σ p q hiff) x

/-- At zero tolerance, the arbitrary-capacity near-one mass of a HOL-induced
crisp profile is exactly the capacity of the predicate's Henkin-model
extension. This is the general theorem behind the weighted-capacity canaries. -/
theorem predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    nearOneMassInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      ν (predicateExtension (Base := Base) (Const := Const) M σ p) := by
  rw [predicateCrispProfileInf_eq_crispIndicator_extension
    (Base := Base) (Const := Const) M σ p]
  exact nearOneMassInf_crispIndicator_eq_cap_of_epsilon_zero
    params hε ν
    (predicateExtension (Base := Base) (Const := Const) M σ p)

/-- At zero tolerance, the arbitrary-capacity fuzzy existential score of a
HOL-induced crisp profile is exactly the capacity of its model extension. -/
theorem predicateFuzzyExistsScoreInf_eq_capacity_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyExistsScoreInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      ν (predicateExtension (Base := Base) (Const := Const) M σ p) := by
  exact predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε ν p

/-- At zero tolerance, the arbitrary-capacity near-zero mass of a HOL-induced
crisp profile is exactly the capacity of the complement of its model
extension. -/
theorem predicateNearZeroMassInf_eq_capacity_compl_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    nearZeroMassInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      ν (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ := by
  rw [predicateCrispProfileInf_eq_crispIndicator_extension
    (Base := Base) (Const := Const) M σ p]
  exact nearZeroMassInf_crispIndicator_eq_cap_compl_of_epsilon_zero
    params hε ν
    (predicateExtension (Base := Base) (Const := Const) M σ p)

/-- At zero tolerance, interval truth for a HOL-induced arbitrary-capacity QFM
profile is just the interval test on the capacity of the predicate extension. -/
theorem predicateFuzzyIntervalHoldsInf_iff_capacity_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyIntervalHoldsInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      params.LPC ≤
          (ν (predicateExtension (Base := Base) (Const := Const) M σ p) : ℝ) ∧
        (ν (predicateExtension (Base := Base) (Const := Const) M σ p) : ℝ) ≤
          params.UPC := by
  unfold fuzzyIntervalHoldsInf
  rw [predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε ν p]

/-- At zero tolerance, fuzzy `ForAll` for a HOL-induced arbitrary-capacity QFM
profile is just a threshold test on the capacity of the predicate extension. -/
theorem predicateFuzzyForAllHoldsInf_iff_capacity_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyForAllHoldsInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      params.PCL ≤
        (ν (predicateExtension (Base := Base) (Const := Const) M σ p) : ℝ) := by
  unfold fuzzyForAllHoldsInf
  rw [predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε ν p]

/-- At zero tolerance, fuzzy `ThereExists` for a HOL-induced arbitrary-capacity
QFM profile is just a threshold test against the complement-capacity of the
predicate extension. This keeps the QFM existential endpoint distinct from
ordinary nonempty existence. -/
theorem predicateFuzzyThereExistsHoldsInf_iff_capacity_compl_extension_of_epsilon_zero
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyThereExistsHoldsInf params ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      params.PCL ≤
        1 - (ν (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ : ℝ) := by
  unfold fuzzyThereExistsHoldsInf
  rw [predicateNearZeroMassInf_eq_capacity_compl_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε ν p]

/-- On a finite nonempty domain, the normalized counting capacity of a set is
`1` exactly when the set is the full carrier.

This is the capacity-level counterpart of
`witnessFraction_eq_zero_iff_forall_not`; it is the endpoint fact needed before
a counting-capacity score can become a definable HOL cut. -/
theorem countingCapacity_eq_one_iff_eq_univ
    {U : Type*} [Fintype U] [Nonempty U] [MeasurableSpace U] (A : Set U) :
    ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) = 1 ↔
      A = Set.univ := by
  classical
  change ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) = 1 ↔
    A = Set.univ
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Fintype.card_ne_zero
  have hden_ne : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast h0
  simp [h0]
  constructor
  · intro hfrac
    have hcardSubtype : Fintype.card A = Fintype.card U := by
      have hnum_eq_real :
          ((Fintype.card A : Nat) : ℝ) = (Fintype.card U : ℝ) := by
        have hfrac' := hfrac
        field_simp [hden_ne] at hfrac'
        simpa using hfrac'
      exact_mod_cast hnum_eq_real
    have hfilter :
        (Finset.univ.filter (fun a : U => a ∈ A)).card = Fintype.card U := by
      simpa using hcardSubtype
    have hfin : Finset.univ.filter (fun a : U => a ∈ A) = Finset.univ :=
      (Finset.card_eq_iff_eq_univ _).mp hfilter
    ext u
    constructor
    · intro _; simp
    · intro _
      have hu : u ∈ Finset.univ.filter (fun a : U => a ∈ A) := by
        rw [hfin]
        simp
      simpa using hu
  · intro hA
    subst hA
    field_simp [hden_ne]
    have hfin :
        @Finset.filter U (Membership.mem (Set.univ : Set U))
          (fun a => Classical.propDecidable (a ∈ (Set.univ : Set U)))
          Finset.univ = (Finset.univ : Finset U) := by
      ext u
      simp
    rw [hfin, Finset.card_univ]

/-- Counting capacity of a HOL predicate extension reaches `1` exactly when
the model satisfies the corresponding HOL universal predicate formula. -/
theorem predicateCountingCapacityExtension_eq_one_iff_models_predicateForAllFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (tau : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M tau)]
    [Nonempty (PredicateObject (Base := Base) (Const := Const) M tau)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M tau)]
    (p : UnaryPredicate (Base := Base) (Const := Const) tau) :
    ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject (Base := Base) (Const := Const) M tau))
        (predicateExtension (Base := Base) (Const := Const) M tau p) : unitInterval) : ℝ) = 1 ↔
      HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) tau p) := by
  rw [countingCapacity_eq_one_iff_eq_univ]
  rw [models_predicateForAllFormula_iff]
  constructor
  · intro hExt x
    have hx : x ∈ predicateExtension (Base := Base) (Const := Const) M tau p := by
      rw [hExt]
      simp
    simpa [predicateExtension] using hx
  · intro hAll
    ext x
    constructor
    · intro _; simp
    · intro _
      exact hAll x

/-- Sugeno aggregation of a HOL-induced crisp profile is exactly the capacity
of its model extension. -/
theorem predicateSugenoScoreInf_eq_capacity_extension
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    sugenoScoreInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      ν (predicateExtension (Base := Base) (Const := Const) M σ p) := by
  unfold sugenoScoreInf
  rw [predicateCrispProfileInf_eq_crispIndicator_extension
    (Base := Base) (Const := Const) M σ p]
  exact FuzzyCapacity.sugenoIntegral_crispIndicator ν
    (predicateExtension (Base := Base) (Const := Const) M σ p)

/-- Under normalized counting capacity, the arbitrary-domain Sugeno score of a
HOL-induced crisp profile reaches `1` exactly at HOL universal predicate truth. -/
theorem predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (tau : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M tau)]
    [Nonempty (PredicateObject (Base := Base) (Const := Const) M tau)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M tau)]
    (p : UnaryPredicate (Base := Base) (Const := Const) tau) :
    ((sugenoScoreInf
        (FuzzyCapacity.countingCapacity
          (U := (PredicateObject (Base := Base) (Const := Const) M tau)))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M tau p) :
        unitInterval) : ℝ) = 1 ↔
      HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) tau p) := by
  rw [predicateSugenoScoreInf_eq_capacity_extension
    (Base := Base) (Const := Const) M tau
    (FuzzyCapacity.countingCapacity
      (U := (PredicateObject (Base := Base) (Const := Const) M tau))) p]
  exact
    predicateCountingCapacityExtension_eq_one_iff_models_predicateForAllFormula
      (Base := Base) (Const := Const) M tau p

/-- Predicate inheritance preserves arbitrary-capacity near-one mass for the
HOL-induced profile. This is the non-counting WM-calc lift of the finite
satisfying-set/QFM bridge. -/
theorem predicateNearOneMassInf_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q) :
    nearOneMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ≤
      nearOneMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) :=
  nearOneMassInf_mono_of_pointwise params.toInf ν
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q)
    (predicateCrispProfileInf_mono_of_inherits
      (Base := Base) (Const := Const) M σ p q hInh)

/-- Predicate inheritance preserves the arbitrary-capacity QFM existential
score. -/
theorem predicateFuzzyExistsScoreInf_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q) :
    fuzzyExistsScoreInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ≤
      fuzzyExistsScoreInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) :=
  fuzzyExistsScoreInf_mono_of_pointwise params.toInf ν
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q)
    (predicateCrispProfileInf_mono_of_inherits
      (Base := Base) (Const := Const) M σ p q hInh)

/-- Predicate inheritance preserves arbitrary-capacity fuzzy universal
acceptance. -/
theorem predicateFuzzyForAllHoldsInf_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (hForAll :
      fuzzyForAllHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p)) :
    fuzzyForAllHoldsInf params.toInf ν
      (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) :=
  fuzzyForAllHoldsInf_mono_of_pointwise params.toInf ν
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q)
    (predicateCrispProfileInf_mono_of_inherits
      (Base := Base) (Const := Const) M σ p q hInh)
    hForAll

/-- Predicate inheritance preserves the arbitrary-capacity Sugeno score. -/
theorem predicateSugenoScoreInf_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q) :
    sugenoScoreInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ≤
      sugenoScoreInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) :=
  sugenoScoreInf_mono ν
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q)
    (predicateCrispProfileInf_mono_of_inherits
      (Base := Base) (Const := Const) M σ p q hInh)

/-- Same-extension replacement preserves arbitrary-capacity near-one mass. -/
theorem predicateNearOneMassInf_eq_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    nearOneMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      nearOneMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfileInf_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves arbitrary-capacity near-zero mass. -/
theorem predicateNearZeroMassInf_eq_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    nearZeroMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) =
      nearZeroMassInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfileInf_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves arbitrary-capacity fuzzy interval
truth. -/
theorem predicateFuzzyIntervalHoldsInf_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyIntervalHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyIntervalHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfileInf_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves arbitrary-capacity fuzzy universal
truth. -/
theorem predicateFuzzyForAllHoldsInf_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyForAllHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyForAllHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfileInf_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves arbitrary-capacity fuzzy existential
truth. -/
theorem predicateFuzzyThereExistsHoldsInf_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (ν : FuzzyCapacity (PredicateObject (Base := Base) (Const := Const) M σ))
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyThereExistsHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyThereExistsHoldsInf params.toInf ν
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfileInf_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Arbitrary-domain near-one mass over the counting capacity reduces exactly
to the finite HOL-induced near-one witness fraction. -/
theorem predicateNearOneMassInf_counting_eq_nearOneFraction
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (nearOneMassInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) : ℝ) =
      nearOneFraction params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  nearOneMassInf_counting_eq_nearOneFractionFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- Arbitrary-domain near-zero mass over the counting capacity reduces exactly
to the finite HOL-induced near-zero witness fraction. -/
theorem predicateNearZeroMassInf_counting_eq_nearZeroFraction
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (nearZeroMassInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) : ℝ) =
      nearZeroFraction params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  nearZeroMassInf_counting_eq_nearZeroFractionFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- The arbitrary-domain existential score over the counting capacity is exactly
the finite HOL-induced QFM existential score. -/
theorem predicateFuzzyExistsScoreInf_counting_eq_fuzzyExistsScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (fuzzyExistsScoreInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) : ℝ) =
      fuzzyExistsScore params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyExistsScoreInf_counting_eq_fuzzyExistsScoreFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- Arbitrary-domain interval truth over the counting capacity is exactly the
finite HOL-induced QFM interval truth. -/
theorem predicateFuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHolds
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyIntervalHoldsInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyIntervalHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHoldsFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- Arbitrary-domain `ForAll` truth over the counting capacity is exactly the
finite HOL-induced QFM `ForAll` truth. -/
theorem predicateFuzzyForAllHoldsInf_counting_iff_fuzzyForAllHolds
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyForAllHoldsInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyForAllHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyForAllHoldsInf_counting_iff_fuzzyForAllHoldsFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- Arbitrary-domain `ThereExists` truth over the counting capacity is exactly
the finite HOL-induced QFM `ThereExists` truth. -/
theorem predicateFuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHolds
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    fuzzyThereExistsHoldsInf params.toInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject (Base := Base) (Const := Const) M σ))
        (predicateCrispProfileInf (Base := Base) (Const := Const) M σ p) ↔
      fuzzyThereExistsHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) :=
  fuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHoldsFin
    params
    (predicateCrispProfile (Base := Base) (Const := Const) M σ p)
    (predicateCrispProfile_mem_unit (Base := Base) (Const := Const) M σ p)

/-- If two HOL predicates have the same extension at a pointed model, every
finite-domain QFM interval truth judgment over their induced crisp profiles is
the same. -/
theorem predicateFuzzyIntervalHolds_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyIntervalHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      fuzzyIntervalHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfile_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves finite-domain QFM `ForAll` truth over
HOL-induced crisp profiles. -/
theorem predicateFuzzyForAllHolds_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyForAllHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      fuzzyForAllHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfile_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

/-- Same-extension replacement preserves finite-domain QFM `ThereExists` truth
over HOL-induced crisp profiles. -/
theorem predicateFuzzyThereExistsHolds_iff_of_pointwiseIff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParams)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hiff :
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x ↔
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x) :
    fuzzyThereExistsHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ p) ↔
      fuzzyThereExistsHolds params
        (predicateCrispProfile (Base := Base) (Const := Const) M σ q) := by
  rw [predicateCrispProfile_eq_of_pointwiseIff
    (Base := Base) (Const := Const) M σ p q hiff]

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
