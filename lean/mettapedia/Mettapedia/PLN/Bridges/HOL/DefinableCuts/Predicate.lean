import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Core

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Predicate-inheritance cut instances -/

/-- The concrete definable cut for full predicate-level inheritance at the
maximal threshold `1`.

This is the first numeric HO-PLN consumer of the formula-level tightness seam:
the numeric event `fullInheritanceStrength(P,Q) ≥ 1` is represented by the HOL
predicate implication formula `∀ x, P x -> Q x`, using the existing
`AbstractInheritance`-based bridge. The nonempty-support hypotheses are the
same hypotheses needed by the full extensional/intensional strength saturation
theorem; they are explicit so the cut does not launder degeneracy. -/
noncomputable def predicateFullInheritanceGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := WithParams Const) σ)]
    (hsubE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ).meaning q).intent.ncard ≠ 0)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula (Base := Base) (Const := WithParams Const) σ p q)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      predicateFullInheritanceStrength
        (Base := Base) (Const := WithParams Const) M.1 σ p q
    threshold := 1
    formula := predicateImpFormula
      (Base := Base) (Const := WithParams Const) σ p q
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      constructor
      · intro hModels
        have hEq :
            predicateFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q = 1 :=
          (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := WithParams Const) M.1 σ p q
            (hsubE M) (hsuperI M)).2 hModels
        change 1 ≤
          predicateFullInheritanceStrength
            (Base := Base) (Const := WithParams Const) M.1 σ p q
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            predicateFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q ≤ 1 :=
          predicateFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ p q
        have hEq :
            predicateFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := WithParams Const) M.1 σ p q
            (hsubE M) (hsuperI M)).1 hEq }

/-- Finite-vocabulary version of `predicateFullInheritanceGeOneCut`.

This is the systems-facing form: a WM-PLN engine usually reasons over a finite
active predicate vocabulary, while each vocabulary item still decodes to a real
HOL predicate in the Henkin model. -/
noncomputable def predicateVocabularyFullInheritanceGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hsubE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := WithParams Const) M.1 σ decode p q
    threshold := 1
    formula := predicateImpFormula
      (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      constructor
      · intro hModels
        have hEq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
            (hsubE M) (hsuperI M)).2 hModels
        change 1 ≤
          predicateVocabularyFullInheritanceStrength
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hEq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
            (hsubE M) (hsuperI M)).1 hEq }

/-- All-predicate crisp similarity at maximal threshold `1` is a definable cut
represented by HOL predicate equivalence.

This is the mathematical counterpart of the finite-vocabulary similarity cut
below. It uses the crisp all-predicate similarity readout, whose value is `1`
exactly when the induced abstract-inheritance relation holds in both
directions. -/
noncomputable def predicateSimilarityGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula (Base := Base) (Const := WithParams Const) σ p q)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      predicateSimilarityStrength
        (Base := Base) (Const := WithParams Const) M.1 σ p q
    threshold := 1
    formula := predicateIffFormula
      (Base := Base) (Const := WithParams Const) σ p q
    paramFree := hφ0
    represents_ge := by
      intro M
      constructor
      · intro hModels
        have hEq :
            predicateSimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q = 1 :=
          (predicateSimilarityStrength_eq_one_iff_models_predicateIffFormula
            (Base := Base) (Const := WithParams Const) M.1 σ p q).2 hModels
        change 1 ≤
          predicateSimilarityStrength
            (Base := Base) (Const := WithParams Const) M.1 σ p q
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            predicateSimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q ≤ 1 := by
          unfold predicateSimilarityStrength
          have hmono :=
            Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.twoInh2Sim_mono_on_unit
              (s_AC₁ :=
                predicateInheritanceStrength
                  (Base := Base) (Const := WithParams Const) M.1 σ p q)
              (s_AC₂ := 1)
              (s_CA₁ :=
                predicateInheritanceStrength
                  (Base := Base) (Const := WithParams Const) M.1 σ q p)
              (s_CA₂ := 1)
              (predicateInheritanceStrength_nonneg
                (Base := Base) (Const := WithParams Const) M.1 σ p q)
              (by norm_num)
              (predicateInheritanceStrength_nonneg
                (Base := Base) (Const := WithParams Const) M.1 σ q p)
              (by norm_num)
              (predicateInheritanceStrength_le_one
                (Base := Base) (Const := WithParams Const) M.1 σ p q)
              (predicateInheritanceStrength_le_one
                (Base := Base) (Const := WithParams Const) M.1 σ q p)
          simpa [Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.twoInh2Sim] using hmono
        have hEq :
            predicateSimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ p q = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateSimilarityStrength_eq_one_iff_models_predicateIffFormula
            (Base := Base) (Const := WithParams Const) M.1 σ p q).1 hEq }

/-- Finite-vocabulary predicate similarity at maximal threshold `1` is a
definable cut represented by HOL predicate equivalence.

This is the first similarity-family cut: it uses `twoInh2Sim` through the live
predicate-similarity bridge, but endpoint tightness still enters only through
the closed HOL sentence `∀x, P x -> Q x` and `∀x, Q x -> P x`. The four support
hypotheses are the two directed full-inheritance supports required by the
similarity saturation theorem. -/
noncomputable def predicateVocabularySimilarityGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      predicateVocabularySimilarityStrength
        (Base := Base) (Const := WithParams Const) M.1 σ decode p q
    threshold := 1
    formula := predicateIffFormula
      (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      constructor
      · intro hModels
        have hEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          (predicateVocabularySimilarityStrength_eq_one_iff_models_predicateIffFormula
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
            (hpE M) (hqI M) (hqE M) (hpI M)).2 hModels
        change 1 ≤
          predicateVocabularySimilarityStrength
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateVocabularySimilarityStrength_eq_one_iff_models_predicateIffFormula
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
            (hpE M) (hqI M) (hqE M) (hpI M)).1 hEq }


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
