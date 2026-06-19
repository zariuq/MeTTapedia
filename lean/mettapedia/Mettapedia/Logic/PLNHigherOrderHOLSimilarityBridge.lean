import Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.Logic.ExtensionalIntensionalDivergence
import Mettapedia.Logic.PLNInferenceRules

/-!
# Higher-Order HOL Predicate Similarity Bridge

This file connects the crisp predicate-equivalence bridge to the existing PLN
similarity formula surface. Predicate-level similarity is not a new relation:
it is mutual abstract inheritance, with `twoInh2Sim` consuming the two directed
crisp inheritance strengths in the collapsed 0/1 case.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.AbstractInheritance

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Directed crisp predicate-inheritance strength: `1` exactly when the
existing abstract-inheritance interpretation validates `p -> q`, otherwise
`0`. This is the bridge from theoremic HOL implication to PLN's numeric
similarity formulas in the crisp special case. -/
noncomputable def predicateInheritanceStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) : ℝ :=
  by
    classical
    exact
      if (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).Inherits p q then 1 else 0

/-- Crisp predicate-inheritance strength is nonnegative. -/
theorem predicateInheritanceStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) :
    0 ≤ predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q := by
  classical
  unfold predicateInheritanceStrength
  split_ifs <;> norm_num

/-- Crisp predicate-inheritance strength is bounded by `1`. -/
theorem predicateInheritanceStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) :
    predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q ≤ 1 := by
  classical
  unfold predicateInheritanceStrength
  split_ifs <;> norm_num

/-- Crisp predicate-inheritance strength reaches `1` exactly when the induced
abstract-inheritance relation holds. -/
theorem predicateInheritanceStrength_eq_one_iff_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) :
    predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1 ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
        (Base := Base) (Const := Const) M σ).Inherits p q := by
  classical
  constructor
  · intro hOne
    unfold predicateInheritanceStrength at hOne
    split_ifs at hOne with hCond
    · simpa [Mettapedia.Logic.AbstractInheritance.Interpretation.inherits_iff] using hCond
    · norm_num at hOne
  · intro hInh
    have hCond :
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).ExtensionalInherits p q ∧
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
            (Base := Base) (Const := Const) M σ).IntensionalInherits p q := by
      simpa [Mettapedia.Logic.AbstractInheritance.Interpretation.inherits_iff] using hInh
    simp [predicateInheritanceStrength, hCond]

/-- Predicate-level crisp similarity computed by the existing PLN
`2inh2sim` rule from the two directed inheritance strengths. -/
noncomputable def predicateSimilarityStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    (predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q)
    (predicateInheritanceStrength (Base := Base) (Const := Const) M σ q p)

/-- The lifted predicate similarity remains symmetric because it reuses PLN's
ordinary symmetric `twoInh2Sim` formula. -/
theorem predicateSimilarityStrength_comm
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) :
    predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q =
      predicateSimilarityStrength (Base := Base) (Const := Const) M σ q p := by
  unfold predicateSimilarityStrength
  exact Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_comm _ _

/-- Mutual predicate inheritance collapses the PLN similarity strength to `1`. -/
theorem predicateSimilarityStrength_eq_one_of_mutualInherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (h :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt
        (Base := Base) (Const := Const) M σ p q) :
    predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 1 := by
  rcases h with ⟨hpq, hqp⟩
  have hpqStrength :
      predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1 := by
    unfold predicateInheritanceStrength
    exact if_pos hpq
  have hqpStrength :
      predicateInheritanceStrength (Base := Base) (Const := Const) M σ q p = 1 := by
    unfold predicateInheritanceStrength
    exact if_pos hqp
  unfold predicateSimilarityStrength
  rw [hpqStrength, hqpStrength]
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

/-- If one directed predicate inheritance fails, the `2inh2sim`-based crisp
similarity collapses to `0`. -/
theorem predicateSimilarityStrength_eq_zero_of_not_inherits_left
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (h :
      ¬ (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
        (Base := Base) (Const := Const) M σ).Inherits p q) :
    predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 0 := by
  have hpqStrength :
      predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q = 0 := by
    unfold predicateInheritanceStrength
    exact if_neg h
  unfold predicateSimilarityStrength
  rw [hpqStrength]
  simp [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

/-- A satisfied HOL predicate-equivalence sentence yields maximal crisp PLN
similarity. -/
theorem predicateSimilarityStrength_eq_one_of_models_predicateIffFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (h : HenkinModel.models M
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
        (Base := Base) (Const := Const) σ p q)) :
    predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 1 :=
  predicateSimilarityStrength_eq_one_of_mutualInherits
    (Base := Base)
    (Const := Const)
    M
    σ
    p
    q
    ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) M σ p q).2 h)

/-- Predicate similarity reaches `1` exactly when the HOL predicate-equivalence
sentence holds in the model.

This is the all-predicate analogue of the finite-vocabulary saturation theorem:
the `twoInh2Sim` arithmetic layer is fully reflected back into the HOL formula
event before it can be used as a completeness-tight definable cut. -/
theorem predicateSimilarityStrength_eq_one_iff_models_predicateIffFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ) :
    predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 1 ↔
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ p q) := by
  constructor
  · intro hsim
    have hBoth :
        predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1 ∧
          predicateInheritanceStrength (Base := Base) (Const := Const) M σ q p = 1 := by
      have hTwo :=
        (Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_eq_one_iff
          (predicateInheritanceStrength (Base := Base) (Const := Const) M σ p q)
          (predicateInheritanceStrength (Base := Base) (Const := Const) M σ q p)
          ⟨predicateInheritanceStrength_nonneg
              (Base := Base) (Const := Const) M σ p q,
           predicateInheritanceStrength_le_one
              (Base := Base) (Const := Const) M σ p q⟩
          ⟨predicateInheritanceStrength_nonneg
              (Base := Base) (Const := Const) M σ q p,
           predicateInheritanceStrength_le_one
              (Base := Base) (Const := Const) M σ q p⟩).1
      exact hTwo (by simpa [predicateSimilarityStrength] using hsim)
    have hMutual :
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt
          (Base := Base) (Const := Const) M σ p q :=
      ⟨(predicateInheritanceStrength_eq_one_iff_inherits
          (Base := Base) (Const := Const) M σ p q).1 hBoth.1,
       (predicateInheritanceStrength_eq_one_iff_inherits
          (Base := Base) (Const := Const) M σ q p).1 hBoth.2⟩
    exact
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) M σ p q).1 hMutual
  · intro hModels
    exact
      predicateSimilarityStrength_eq_one_of_models_predicateIffFormula
        (Base := Base) (Const := Const) M σ p q hModels

/-- A proved HOL predicate-equivalence sentence induces maximal crisp PLN
similarity at every pointed Henkin model. -/
theorem holProvable_predicateIffFormula_implies_similarityStrength_one
    (σ : Ty Base)
    (p q : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (h :
      Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
        (Const := Const)
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ p q)) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 1 := by
  intro M
  exact
    predicateSimilarityStrength_eq_one_of_mutualInherits
      (Base := Base)
      (Const := Const)
      M
      σ
      p
      q
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.holProvable_predicateIffFormula_implies_mutualInherits
          (Base := Base) (Const := Const) σ p q h M)

/-! ## Saturated analogy transfer -/

/-- Saturated predicate similarity on the source side transfers saturated
predicate inheritance. If `p` and `q` are equivalent at similarity strength
`1`, and `q` fully inherits `r`, then `p` fully inherits `r`.

This is the exact-threshold analogy-transfer rule: it reuses the similarity
bridge only to recover the HOL equivalence event, then composes ordinary
predicate implication through the existing inheritance bridge. -/
theorem predicateFullInheritanceStrength_eq_one_of_source_similarity
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)]
    (p q r : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (hpExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning p).extent.ncard ≠ 0)
    (hqExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning q).extent.ncard ≠ 0)
    (hrIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning r).intent.ncard ≠ 0)
    (hsim :
      predicateSimilarityStrength (Base := Base) (Const := Const) M σ p q = 1)
    (hqr :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength
        (Base := Base) (Const := Const) M σ q r = 1) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength
      (Base := Base) (Const := Const) M σ p r = 1 := by
  have hIff :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ p q) :=
    (predicateSimilarityStrength_eq_one_iff_models_predicateIffFormula
      (Base := Base) (Const := Const) M σ p q).1 hsim
  have hpqModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ p q) :=
    (HenkinModel.models_and M).mp hIff |>.1
  have hqrModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ q r) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ q r hqExtent hrIntent).1 hqr
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p r hpExtent hrIntent).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ p q r hpqModels hqrModels

/-- Saturated predicate similarity on the target side transfers saturated
predicate inheritance. If `q` and `r` are equivalent at similarity strength
`1`, and `p` fully inherits `q`, then `p` fully inherits `r`. -/
theorem predicateFullInheritanceStrength_eq_one_of_target_similarity
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)]
    (p q r : Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := Base) (Const := Const) σ)
    (hpExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning p).extent.ncard ≠ 0)
    (hqIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning q).intent.ncard ≠ 0)
    (hrIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
          (Base := Base) (Const := Const) M σ).meaning r).intent.ncard ≠ 0)
    (hpq :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength
        (Base := Base) (Const := Const) M σ p q = 1)
    (hsim :
      predicateSimilarityStrength (Base := Base) (Const := Const) M σ q r = 1) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength
      (Base := Base) (Const := Const) M σ p r = 1 := by
  have hpqModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ p q) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p q hpExtent hqIntent).1 hpq
  have hIff :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ q r) :=
    (predicateSimilarityStrength_eq_one_iff_models_predicateIffFormula
      (Base := Base) (Const := Const) M σ q r).1 hsim
  have hqrModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ q r) :=
    (HenkinModel.models_and M).mp hIff |>.1
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p r hpExtent hrIntent).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ p q r hpqModels hqrModels

/-! ## Finite working-vocabulary similarity -/

/-- Predicate-level pure extensional inheritance strength on a finite active
vocabulary. This is the object-side half of higher-order predicate inheritance:
the decoded HOL predicates supply the extents, while the grading itself is the
existing extensional/intensional inheritance machinery. -/
noncomputable def predicateVocabularyPureExtensionalStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.ExtensionalIntensionalDivergence.pureExtensionalStrength
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode) p q

/-- Predicate-level pure intensional inheritance strength on a finite active
vocabulary. Here the attributes are the working predicate symbols themselves,
so the strength measures shared predicate-pattern support rather than merely
object overlap. -/
noncomputable def predicateVocabularyPureIntensionalStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.ExtensionalIntensionalDivergence.pureIntensionalStrength
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyPureExtensionalStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) :
    0 ≤ predicateVocabularyPureExtensionalStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureExtensionalStrength_nonneg
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyPureExtensionalStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) :
    predicateVocabularyPureExtensionalStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureExtensionalStrength_le_one
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyPureIntensionalStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ predicateVocabularyPureIntensionalStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureIntensionalStrength_nonneg
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyPureIntensionalStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularyPureIntensionalStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureIntensionalStrength_le_one
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyPureExtensionalStrength_eq_one_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred)
    (hpE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0) :
    predicateVocabularyPureExtensionalStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).ExtensionalInherits p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureExtensionalStrength_eq_one_iff
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q hpE

theorem predicateVocabularyPureIntensionalStrength_eq_one_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0) :
    predicateVocabularyPureIntensionalStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.pureIntensionalStrength_eq_one_iff
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q hqI

/-- Symmetric similarity built only from the pure extensional half of the
predicate-vocabulary interpretation. -/
noncomputable def predicateVocabularyPureExtensionalSimilarityStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    (predicateVocabularyPureExtensionalStrength
      (Base := Base) (Const := Const) M σ decode p q)
    (predicateVocabularyPureExtensionalStrength
      (Base := Base) (Const := Const) M σ decode q p)

/-- Symmetric similarity built only from the pure intensional half of the
predicate-vocabulary interpretation. This is the first explicit HO seam for
predicate-pattern similarity; PAT/ASSOC-style evidence should refine this
surface rather than create a separate predicate-similarity relation. -/
noncomputable def predicateVocabularyPureIntensionalSimilarityStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    (predicateVocabularyPureIntensionalStrength
      (Base := Base) (Const := Const) M σ decode p q)
    (predicateVocabularyPureIntensionalStrength
      (Base := Base) (Const := Const) M σ decode q p)

/-- Pattern-side/intensional inclusion target for finite predicate vocabularies:
`p` intensionally inherits from `q` exactly when every pattern/attribute in
`q`'s intent is also in `p`'s intent. PAT/ASSOC evidence should discharge this
kind of inclusion instead of defining a separate higher-order similarity
relation. -/
def predicateVocabularyIntentSubset
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p q : Pred) : Prop :=
  ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).meaning q).intent ⊆
    ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).meaning p).intent

/-- Same-intent predicate vocabulary entries: the direct theorem target for
predicate-pattern equivalence. -/
def predicateVocabularySameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p q : Pred) : Prop :=
  ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).meaning p).intent =
    ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).meaning q).intent

theorem predicateVocabularyIntensionalInherits_iff_intentSubset
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p q : Pred) :
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q ↔
      predicateVocabularyIntentSubset
        (Base := Base) (Const := Const) M σ decode p q := by
  rfl

theorem predicateVocabularySameIntent_iff_mutualIntensional
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p q : Pred) :
    predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode p q ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q ∧
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits q p := by
  unfold predicateVocabularySameIntent
  constructor
  · intro hEq
    constructor
    · intro attr hAttr
      simpa [hEq] using hAttr
    · intro attr hAttr
      simpa [hEq] using hAttr
  · rintro ⟨hpq, hqp⟩
    exact Set.Subset.antisymm hqp hpq

theorem predicateVocabularyPureExtensionalSimilarityStrength_comm
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) :
    predicateVocabularyPureExtensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q =
      predicateVocabularyPureExtensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode q p := by
  unfold predicateVocabularyPureExtensionalSimilarityStrength
  exact Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_comm _ _

theorem predicateVocabularyPureIntensionalSimilarityStrength_comm
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularyPureIntensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q =
      predicateVocabularyPureIntensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode q p := by
  unfold predicateVocabularyPureIntensionalSimilarityStrength
  exact Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_comm _ _

theorem predicateVocabularyPureExtensionalSimilarityStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) :
    0 ≤ predicateVocabularyPureExtensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  unfold predicateVocabularyPureExtensionalSimilarityStrength
  exact
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_nonneg _ _
      ⟨predicateVocabularyPureExtensionalStrength_nonneg
          (Base := Base) (Const := Const) M σ decode p q,
       predicateVocabularyPureExtensionalStrength_le_one
          (Base := Base) (Const := Const) M σ decode p q⟩
      ⟨predicateVocabularyPureExtensionalStrength_nonneg
          (Base := Base) (Const := Const) M σ decode q p,
       predicateVocabularyPureExtensionalStrength_le_one
          (Base := Base) (Const := Const) M σ decode q p⟩

theorem predicateVocabularyPureIntensionalSimilarityStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ predicateVocabularyPureIntensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  unfold predicateVocabularyPureIntensionalSimilarityStrength
  exact
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_nonneg _ _
      ⟨predicateVocabularyPureIntensionalStrength_nonneg
          (Base := Base) (Const := Const) M σ decode p q,
       predicateVocabularyPureIntensionalStrength_le_one
          (Base := Base) (Const := Const) M σ decode p q⟩
      ⟨predicateVocabularyPureIntensionalStrength_nonneg
          (Base := Base) (Const := Const) M σ decode q p,
       predicateVocabularyPureIntensionalStrength_le_one
          (Base := Base) (Const := Const) M σ decode q p⟩

theorem predicateVocabularyPureExtensionalSimilarityStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred) :
    predicateVocabularyPureExtensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  unfold predicateVocabularyPureExtensionalSimilarityStrength
  have hmono :=
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_mono_on_unit
      (s_AC₁ :=
        predicateVocabularyPureExtensionalStrength
          (Base := Base) (Const := Const) M σ decode p q)
      (s_AC₂ := 1)
      (s_CA₁ :=
        predicateVocabularyPureExtensionalStrength
          (Base := Base) (Const := Const) M σ decode q p)
      (s_CA₂ := 1)
      (predicateVocabularyPureExtensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode p q)
      (by norm_num)
      (predicateVocabularyPureExtensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode q p)
      (by norm_num)
      (predicateVocabularyPureExtensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode p q)
      (predicateVocabularyPureExtensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode q p)
  simpa [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim] using hmono

theorem predicateVocabularyPureIntensionalSimilarityStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularyPureIntensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  unfold predicateVocabularyPureIntensionalSimilarityStrength
  have hmono :=
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_mono_on_unit
      (s_AC₁ :=
        predicateVocabularyPureIntensionalStrength
          (Base := Base) (Const := Const) M σ decode p q)
      (s_AC₂ := 1)
      (s_CA₁ :=
        predicateVocabularyPureIntensionalStrength
          (Base := Base) (Const := Const) M σ decode q p)
      (s_CA₂ := 1)
      (predicateVocabularyPureIntensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode p q)
      (by norm_num)
      (predicateVocabularyPureIntensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode q p)
      (by norm_num)
      (predicateVocabularyPureIntensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode p q)
      (predicateVocabularyPureIntensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode q p)
  simpa [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim] using hmono

theorem predicateVocabularyPureExtensionalSimilarityStrength_eq_one_of_mutualExtensional
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred)
    (hpE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hpq :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).ExtensionalInherits p q)
    (hqp :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).ExtensionalInherits q p) :
    predicateVocabularyPureExtensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q = 1 := by
  have hpqStrength :
      predicateVocabularyPureExtensionalStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 :=
    (predicateVocabularyPureExtensionalStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ decode p q hpE).2 hpq
  have hqpStrength :
      predicateVocabularyPureExtensionalStrength
        (Base := Base) (Const := Const) M σ decode q p = 1 :=
    (predicateVocabularyPureExtensionalStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ decode q p hqE).2 hqp
  unfold predicateVocabularyPureExtensionalSimilarityStrength
  rw [hpqStrength, hqpStrength]
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

theorem predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_mutualIntensional
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hpq :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q)
    (hqp :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits q p) :
    predicateVocabularyPureIntensionalSimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q = 1 := by
  have hpqStrength :
      predicateVocabularyPureIntensionalStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 :=
    (predicateVocabularyPureIntensionalStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ decode p q hqI).2 hpq
  have hqpStrength :
      predicateVocabularyPureIntensionalStrength
        (Base := Base) (Const := Const) M σ decode q p = 1 :=
    (predicateVocabularyPureIntensionalStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ decode q p hpI).2 hqp
  unfold predicateVocabularyPureIntensionalSimilarityStrength
  rw [hpqStrength, hqpStrength]
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

/-- The pure extensional half of finite-vocabulary predicate similarity is
exactly mutual extensional inheritance, provided both source extensions are
nonempty. This is the higher-order counterpart of PLN's ordinary
inheritance-to-similarity rule, routed through the existing
`ExtensionalIntensionalDivergence` interpretation. -/
theorem predicateVocabularyPureExtensionalSimilarityStrength_eq_one_iff_mutualExtensional
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    (p q : Pred)
    (hpE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0) :
    predicateVocabularyPureExtensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).ExtensionalInherits p q ∧
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).ExtensionalInherits q p := by
  let I :=
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode
  have hPQ :
      0 ≤ predicateVocabularyPureExtensionalStrength
            (Base := Base) (Const := Const) M σ decode p q ∧
        predicateVocabularyPureExtensionalStrength
            (Base := Base) (Const := Const) M σ decode p q ≤ 1 :=
    ⟨predicateVocabularyPureExtensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode p q,
      predicateVocabularyPureExtensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode p q⟩
  have hQP :
      0 ≤ predicateVocabularyPureExtensionalStrength
            (Base := Base) (Const := Const) M σ decode q p ∧
        predicateVocabularyPureExtensionalStrength
            (Base := Base) (Const := Const) M σ decode q p ≤ 1 :=
    ⟨predicateVocabularyPureExtensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode q p,
      predicateVocabularyPureExtensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode q p⟩
  unfold predicateVocabularyPureExtensionalSimilarityStrength
  rw [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_eq_one_iff _ _ hPQ hQP]
  constructor
  · rintro ⟨hpq, hqp⟩
    exact
      ⟨(predicateVocabularyPureExtensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode p q hpE).1 hpq,
       (predicateVocabularyPureExtensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode q p hqE).1 hqp⟩
  · rintro ⟨hpq, hqp⟩
    exact
      ⟨(predicateVocabularyPureExtensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode p q hpE).2 hpq,
       (predicateVocabularyPureExtensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode q p hqE).2 hqp⟩

/-- The pure intensional half of finite-vocabulary predicate similarity is
exactly mutual intensional inheritance, provided both target intensions are
nonempty in the two directed reads. This is the hook for PAT/ASSOC-style
predicate-pattern evidence: that evidence should establish these existing
intensional-inheritance hypotheses, not define a parallel similarity relation. -/
theorem predicateVocabularyPureIntensionalSimilarityStrength_eq_one_iff_mutualIntensional
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0) :
    predicateVocabularyPureIntensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q ∧
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits q p := by
  let I :=
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode
  have hPQ :
      0 ≤ predicateVocabularyPureIntensionalStrength
            (Base := Base) (Const := Const) M σ decode p q ∧
        predicateVocabularyPureIntensionalStrength
            (Base := Base) (Const := Const) M σ decode p q ≤ 1 :=
    ⟨predicateVocabularyPureIntensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode p q,
      predicateVocabularyPureIntensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode p q⟩
  have hQP :
      0 ≤ predicateVocabularyPureIntensionalStrength
            (Base := Base) (Const := Const) M σ decode q p ∧
        predicateVocabularyPureIntensionalStrength
            (Base := Base) (Const := Const) M σ decode q p ≤ 1 :=
    ⟨predicateVocabularyPureIntensionalStrength_nonneg
        (Base := Base) (Const := Const) M σ decode q p,
      predicateVocabularyPureIntensionalStrength_le_one
        (Base := Base) (Const := Const) M σ decode q p⟩
  unfold predicateVocabularyPureIntensionalSimilarityStrength
  rw [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_eq_one_iff _ _ hPQ hQP]
  constructor
  · rintro ⟨hpq, hqp⟩
    exact
      ⟨(predicateVocabularyPureIntensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode p q hqI).1 hpq,
       (predicateVocabularyPureIntensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode q p hpI).1 hqp⟩
  · rintro ⟨hpq, hqp⟩
    exact
      ⟨(predicateVocabularyPureIntensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode p q hqI).2 hpq,
       (predicateVocabularyPureIntensionalStrength_eq_one_iff
          (Base := Base) (Const := Const) M σ decode q p hpI).2 hqp⟩

/-- Pure intensional predicate similarity is `1` exactly when the two finite
vocabulary entries have the same intent/pattern attribute set. This is the
systems-facing target for PAT/ASSOC: once pattern evidence proves same intent,
the ordinary PLN similarity rule supplies the strength. -/
theorem predicateVocabularyPureIntensionalSimilarityStrength_eq_one_iff_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0) :
    predicateVocabularyPureIntensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode p q := by
  exact
    (predicateVocabularyPureIntensionalSimilarityStrength_eq_one_iff_mutualIntensional
        (Base := Base) (Const := Const) M σ decode p q hpI hqI).trans
      (predicateVocabularySameIntent_iff_mutualIntensional
        (Base := Base) (Const := Const) M σ decode p q).symm

theorem predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hSame :
      predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode p q) :
    predicateVocabularyPureIntensionalSimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 :=
  (predicateVocabularyPureIntensionalSimilarityStrength_eq_one_iff_sameIntent
    (Base := Base) (Const := Const) M σ decode p q hpI hqI).2 hSame

/-- Predicate-level similarity on a finite active vocabulary, computed by
PLN's ordinary `2inh2sim` rule from the two directed full
extensional/intensional inheritance strengths. This is the systems-facing
version of higher-order predicate similarity: the vocabulary is finite, while
each vocabulary item still decodes to a genuine closed HOL unary predicate. -/
noncomputable def predicateVocabularySimilarityStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode p q)
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode q p)

/-- Finite-vocabulary predicate similarity is symmetric because the underlying
PLN `2inh2sim` rule is symmetric. -/
theorem predicateVocabularySimilarityStrength_comm
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q =
      predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) M σ decode q p := by
  unfold predicateVocabularySimilarityStrength
  exact Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_comm _ _

/-- The finite-vocabulary similarity strength stays inside the probability
unit interval on the lower side. -/
theorem predicateVocabularySimilarityStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ predicateVocabularySimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  unfold predicateVocabularySimilarityStrength
  exact
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_nonneg _ _
      ⟨Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
            (Base := Base) (Const := Const) M σ decode p q,
       Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := Const) M σ decode p q⟩
      ⟨Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
            (Base := Base) (Const := Const) M σ decode q p,
       Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := Const) M σ decode q p⟩

/-- The finite-vocabulary similarity strength is bounded above by `1`. This is
proved by monotonicity of `2inh2sim` on the unit square, not by a new
predicate-specific similarity semantics. -/
theorem predicateVocabularySimilarityStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularySimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  unfold predicateVocabularySimilarityStrength
  have hmono :=
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_mono_on_unit
      (s_AC₁ :=
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode p q)
      (s_AC₂ := 1)
      (s_CA₁ :=
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode q p)
      (s_CA₂ := 1)
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
          (Base := Base) (Const := Const) M σ decode p q)
      (by norm_num)
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
          (Base := Base) (Const := Const) M σ decode q p)
      (by norm_num)
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
          (Base := Base) (Const := Const) M σ decode p q)
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
          (Base := Base) (Const := Const) M σ decode q p)
  simpa [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim] using hmono

/-- If both directed finite-vocabulary full inheritance strengths are certain,
the induced predicate similarity is certain. -/
theorem predicateVocabularySimilarityStrength_eq_one_of_mutualFullInheritance
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred)
    (hpq :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := Const) M σ decode p q = 1)
    (hqp :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := Const) M σ decode q p = 1) :
    predicateVocabularySimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q = 1 := by
  unfold predicateVocabularySimilarityStrength
  rw [hpq, hqp]
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

/-- A modeled HOL predicate equivalence yields maximal finite-vocabulary
predicate similarity, provided the finite-vocabulary full-inheritance supports
needed for the two directed bridges are nonempty. -/
theorem predicateVocabularySimilarityStrength_eq_one_of_models_predicateIffFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred)
    (hpE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (h :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
            (Base := Base) (Const := Const) σ (decode p) (decode q))) :
    predicateVocabularySimilarityStrength
      (Base := Base) (Const := Const) M σ decode p q = 1 := by
  have hAnd := (HenkinModel.models_and M).mp h
  apply
    predicateVocabularySimilarityStrength_eq_one_of_mutualFullInheritance
      (Base := Base) (Const := Const) M σ decode p q
  · exact
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ decode p q hpE hqI).2 hAnd.1
  · exact
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ decode q p hqE hpI).2 hAnd.2

/-- Under the same nonempty-support hypotheses needed by the directed
full-inheritance bridges, finite-vocabulary predicate similarity reaches `1`
exactly when the HOL predicate-equivalence sentence holds in the model.

This is the saturation theorem needed before predicate similarity can be used as
a definable numeric cut: it prevents the `2inh2sim` value layer from asserting
endpoint tightness without recovering the corresponding HOL formula event. -/
theorem predicateVocabularySimilarityStrength_eq_one_iff_models_predicateIffFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred)
    (hpE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0) :
    predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
            (Base := Base) (Const := Const) σ (decode p) (decode q)) := by
  constructor
  · intro hsim
    have hPQunit :
        0 ≤ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode p q ∧
          Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode p q ≤ 1 :=
      ⟨Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
          (Base := Base) (Const := Const) M σ decode p q,
       Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
          (Base := Base) (Const := Const) M σ decode p q⟩
    have hQPunit :
        0 ≤ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode q p ∧
          Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode q p ≤ 1 :=
      ⟨Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_nonneg
          (Base := Base) (Const := Const) M σ decode q p,
       Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_le_one
          (Base := Base) (Const := Const) M σ decode q p⟩
    have hBoth :
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode p q = 1 ∧
          Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode q p = 1 := by
      have hTwo :=
        (Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_eq_one_iff
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode p q)
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := Const) M σ decode q p)
          hPQunit hQPunit).1
      exact hTwo (by simpa [predicateVocabularySimilarityStrength] using hsim)
    have hpqModels :
        HenkinModel.models M
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
            (Base := Base) (Const := Const) σ (decode p) (decode q)) :=
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
        (Base := Base) (Const := Const) M σ decode p q hpE hqI).1 hBoth.1
    have hqpModels :
        HenkinModel.models M
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
            (Base := Base) (Const := Const) σ (decode q) (decode p)) :=
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
        (Base := Base) (Const := Const) M σ decode q p hqE hpI).1 hBoth.2
    exact (HenkinModel.models_and M).mpr ⟨hpqModels, hqpModels⟩
  · intro hModels
    exact
      predicateVocabularySimilarityStrength_eq_one_of_models_predicateIffFormula
        (Base := Base) (Const := Const) M σ decode p q hpE hqI hqE hpI hModels

/-- Finite-vocabulary saturated analogy transfer on the source side. If the
source predicate is similar to an intermediate predicate at strength `1`, and
the intermediate predicate fully inherits the target, then the source fully
inherits the target.

The proof recovers the HOL equivalence event from the similarity endpoint and
then composes predicate implication through the already-shared
extensional/intensional inheritance bridge. -/
theorem predicateVocabularyFullInheritanceStrength_eq_one_of_source_similarity
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q r : Pred)
    (hpExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hpIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard ≠ 0)
    (hqExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hqIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hrIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning r).intent.ncard ≠ 0)
    (hsim :
      predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) M σ decode p q = 1)
    (hqr :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode q r = 1) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode p r = 1 := by
  have hIff :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ (decode p) (decode q)) :=
    (predicateVocabularySimilarityStrength_eq_one_iff_models_predicateIffFormula
      (Base := Base) (Const := Const) M σ decode p q
      hpExtent hqIntent hqExtent hpIntent).1 hsim
  have hpqModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ (decode p) (decode q)) :=
    (HenkinModel.models_and M).mp hIff |>.1
  have hqrModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ (decode q) (decode r)) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode q r hqExtent hrIntent).1 hqr
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode p r hpExtent hrIntent).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ (decode p) (decode q) (decode r)
        hpqModels hqrModels

/-- Finite-vocabulary saturated analogy transfer on the target side. If the
target predicate is similar to an intermediate predicate at strength `1`, and
the source fully inherits the intermediate predicate, then the source fully
inherits the target. -/
theorem predicateVocabularyFullInheritanceStrength_eq_one_of_target_similarity
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q r : Pred)
    (hpExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hqExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hrExtent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning r).extent.ncard ≠ 0)
    (hrIntent :
      ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning r).intent.ncard ≠ 0)
    (hpq :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode p q = 1)
    (hsim :
      predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) M σ decode q r = 1) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode p r = 1 := by
  have hpqModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ (decode p) (decode q)) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode p q hpExtent hqIntent).1 hpq
  have hIff :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
          (Base := Base) (Const := Const) σ (decode q) (decode r)) :=
    (predicateVocabularySimilarityStrength_eq_one_iff_models_predicateIffFormula
      (Base := Base) (Const := Const) M σ decode q r
      hqExtent hrIntent hrExtent hqIntent).1 hsim
  have hqrModels :
      HenkinModel.models M
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := Base) (Const := Const) σ (decode q) (decode r)) :=
    (HenkinModel.models_and M).mp hIff |>.1
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode p r hpExtent hrIntent).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ (decode p) (decode q) (decode r)
        hpqModels hqrModels

end Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
