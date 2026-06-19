import Mettapedia.Logic.PLNHigherOrderHOLCompletenessTightness
import Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge

/-!
# Definable Numeric Cuts for Completeness-Tight HO-PLN

The formula-level completeness theorem is endpoint-tight over
`ExtensionalTheoryModel`. Numeric higher-order PLN quantities may inherit that
tightness only after their threshold events are represented by actual closed HOL
formulae. This file formalizes that seam without claiming that arbitrary
numeric consumers are already definable.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLDefinableCuts

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
open Mettapedia.Logic.PLNFirstOrder
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A numeric observable over the extensional canonical model family is
`definably cut` at a threshold when a param-free closed HOL formula represents
exactly the event that the observable is at least that threshold.

This is a certificate, not an existence claim: numeric HO-PLN consumers remain
semantic envelopes until such certificates are built for their threshold events.
-/
structure ExtensionalDefinableCut
    (T : ClosedTheorySet (WithParams Const)) where
  score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ
  threshold : ℝ
  formula : ClosedFormula (WithParams Const)
  paramFree : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) formula
  represents_ge :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      HenkinModel.models M.1 formula ↔ threshold ≤ score M

/-- The interval associated with a definable cut is just the existing
formula-level extensional interval for the representing cut formula. -/
noncomputable def ExtensionalDefinableCut.intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    Interval :=
  extensionalTheoryCredalHOLFormulaIntervalOfConsistent
    (Base := Base) (Const := Const) T enum henum hCons hT0 hEM C.formula

/-- Endpoint tightness for a definable numeric cut: lower endpoint `1` exactly
means that the theory proves the representing cut formula. -/
theorem ExtensionalDefinableCut.lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T C.formula := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_lower_eq_one_iff_provable
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree

/-- Endpoint tightness for a definable numeric cut: upper endpoint `0` exactly
means that the theory proves the negation of the representing cut formula. -/
theorem ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not C.formula) := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree

/-- If the theory does not prove a definable threshold formula, completeness
supplies an extensional countermodel and the lower endpoint of the cut interval
is attained at `0`. -/
theorem ExtensionalDefinableCut.lower_eq_zero_of_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T C.formula) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 0 := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_lower_eq_zero_of_not_provable
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree hNotProv

/-- If the theory does not refute a definable threshold formula, completeness
supplies an extensional model of the threshold event and the upper endpoint of
the cut interval is attained at `1`. -/
theorem ExtensionalDefinableCut.upper_eq_one_of_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hNotProvNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not C.formula)) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 1 := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_upper_eq_one_of_not_provable_not
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree hNotProvNot

/-- Open-endpoint tightness for a definable cut: lower endpoint `0` exactly
means that the theory does not prove the representing cut formula. -/
theorem ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T C.formula := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree

/-- Open-endpoint tightness for a definable cut: upper endpoint `1` exactly
means that the theory does not prove the negation of the representing cut
formula. -/
theorem ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not C.formula) := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree

/-- A definable cut has width zero exactly when the theory decides its
representing threshold formula. -/
theorem ExtensionalDefinableCut.width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T C.formula ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not C.formula) := by
  exact
    extensionalTheoryCredalHOLFormulaInterval_width_eq_zero_iff_decides
      (Base := Base) (Const := Const) (T := T) (χ := C.formula)
      enum henum hCons hT0 hEM C.paramFree

/-- Semantic reading of the lower endpoint: it is `1` exactly when every
extensional theory model satisfies the numeric threshold event. -/
theorem ExtensionalDefinableCut.lower_eq_one_iff_forall_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M := by
  constructor
  · intro hLower M
    have hProv :
        ClosedTheorySet.Provable (Const := WithParams Const) T C.formula :=
      (C.lower_eq_one_iff_provable
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).mp hLower
    exact
      (C.represents_ge M).mp
        (models_of_provable_of_functionsRespectEqv
          (Base := Base) (Const := Const) hProv M.1 M.2.1 M.2.2)
  · intro hAll
    letI : Nonempty (ExtensionalTheoryModel (Base := Base) (Const := Const) T) :=
      nonempty_extensionalTheoryModel_of_consistent_classical
        (Base := Base) (Const := Const) (T := T)
        enum henum hCons hT0 hEM
    have hEq :
        extensionalTheoryCredalHOLFormulaInterval
          (Base := Base) (Const := Const) T C.formula = constInterval 1 :=
      extensionalTheoryCredalHOLFormulaInterval_eq_const_one_of_all_models
        (Base := Base) (Const := Const) (T := T) (φ := C.formula)
        (fun M => (C.represents_ge M).mpr (hAll M))
    unfold ExtensionalDefinableCut.intervalOfConsistent
    unfold extensionalTheoryCredalHOLFormulaIntervalOfConsistent
    simp [hEq, constInterval]

/-- Semantic reading of the upper endpoint: it is `0` exactly when every
extensional theory model fails the numeric threshold event. -/
theorem ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ C.threshold ≤ C.score M := by
  constructor
  · intro hUpper M hGe
    have hProvNot :
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not C.formula) :=
      (C.upper_eq_zero_iff_provable_not
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).mp hUpper
    have hNotModels : ¬ HenkinModel.models M.1 C.formula :=
      (HenkinModel.models_not M.1).mp
        (models_of_provable_of_functionsRespectEqv
          (Base := Base) (Const := Const) hProvNot M.1 M.2.1 M.2.2)
    exact hNotModels ((C.represents_ge M).mpr hGe)
  · intro hAll
    letI : Nonempty (ExtensionalTheoryModel (Base := Base) (Const := Const) T) :=
      nonempty_extensionalTheoryModel_of_consistent_classical
        (Base := Base) (Const := Const) (T := T)
        enum henum hCons hT0 hEM
    have hEq :
        extensionalTheoryCredalHOLFormulaInterval
          (Base := Base) (Const := Const) T C.formula = constInterval 0 :=
      extensionalTheoryCredalHOLFormulaInterval_eq_const_zero_of_all_not_models
        (Base := Base) (Const := Const) (T := T) (φ := C.formula)
        (fun M hModels => hAll M ((C.represents_ge M).mp hModels))
    unfold ExtensionalDefinableCut.intervalOfConsistent
    unfold extensionalTheoryCredalHOLFormulaIntervalOfConsistent
    simp [hEq, constInterval]

/-- Concrete positive example: the indicator score of a closed formula is
definably cut at threshold `1` by the formula itself. -/
noncomputable def formulaIndicatorGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T := by
  classical
  exact
    { score := fun M =>
        if HenkinModel.models M.1 φ then (1 : ℝ) else 0
      threshold := 1
      formula := φ
      paramFree := hφ0
      represents_ge := by
        intro M
        by_cases h : HenkinModel.models M.1 φ
        · simp [h]
        · simp [h] }

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
            Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_mono_on_unit
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
          simpa [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim] using hmono
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

/-! ## QFM / fuzzy-quantifier cut instances -/

/-- At the strict finite-QFM endpoint, PLN-2008-style fuzzy `ForAll`
acceptance is a definable threshold event represented by the ordinary HOL
universal predicate formula.

This is deliberately the endpoint theorem, not the general fuzzy case:
arbitrary tolerance/capacity scores remain semantic numeric envelopes until
their threshold events are separately represented by closed HOL formulae. -/
noncomputable def predicateFuzzyForAllCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      by
      classical
      letI := hObj M
      exact
      if fuzzyForAllHolds params
          (predicateCrispProfile
            (Base := Base) (Const := WithParams Const) M.1 σ p) then
        (1 : ℝ)
      else
        0
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        change 1 ≤
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0)
        simp [hHolds]
      · intro hGe
        by_cases hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p)
        · exact
            (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
              (Base := Base) (Const := WithParams Const) M.1 σ params p
              hε0 hPCL1).1 hHolds
        · have hNoGe :
              ¬ 1 ≤
                (if fuzzyForAllHolds params
                    (predicateCrispProfile
                      (Base := Base) (Const := WithParams Const) M.1 σ p) then
                  (1 : ℝ)
                else
                  0) := by
            simp [hHolds]
          exact False.elim (hNoGe hGe) }

/-- At the strict finite-QFM endpoint, maximal existential-style near-one
score is also represented by the HOL universal predicate formula.

This is an intentionally clarifying theorem about the PLN-2008 QFM layer:
`fuzzyExistsScore` is the near-one mass, so threshold `1` says that every
admissible object is near-one. In the crisp endpoint this is HOL `ForAll`, not
ordinary logical `Exists`. -/
noncomputable def predicateFuzzyExistsScoreGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      fuzzyExistsScore params
        (predicateCrispProfile
          (Base := Base) (Const := WithParams Const) M.1 σ p)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        unfold fuzzyForAllHolds at hHolds
        change 1 ≤
          fuzzyExistsScore params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
        simpa [fuzzyExistsScore, hPCL1] using hHolds
      · intro hGe
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) := by
          unfold fuzzyForAllHolds
          simpa [fuzzyExistsScore, hPCL1] using hGe
        exact
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).1 hHolds }

/-- At the strict finite-QFM endpoint, PLN-2008-style fuzzy `ThereExists`
acceptance at threshold `1` is also represented by the HOL universal predicate
formula.

This is another clarifying cut certificate: the maximal-threshold QFM
existential-style check says that no admissible object is near-zero. For a crisp
profile at `epsilon = 0`, that is exactly universal HOL truth, not ordinary
logical existential truth. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      by
      classical
      letI := hObj M
      exact
      if fuzzyThereExistsHolds params
          (predicateCrispProfile
            (Base := Base) (Const := WithParams Const) M.1 σ p) then
        (1 : ℝ)
      else
        0
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyThereExistsHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        change 1 ≤
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0)
        simp [hHolds]
      · intro hGe
        by_cases hHolds :
            fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p)
        · exact
            (predicateFuzzyThereExistsHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
              (Base := Base) (Const := WithParams Const) M.1 σ params p
              hε0 hPCL1).1 hHolds
        · have hNoGe :
              ¬ 1 ≤
                (if fuzzyThereExistsHolds params
                    (predicateCrispProfile
                      (Base := Base) (Const := WithParams Const) M.1 σ p) then
                  (1 : ℝ)
                else
                  0) := by
            simp [hHolds]
          exact False.elim (hNoGe hGe) }

/-! ## Calibrated capacity / Sugeno cut instances -/

/-- A capacity-family calibration certificate for a HOL predicate.

The certificate says that, for every extensional theory model, the chosen
capacity on the predicate-object carrier makes Sugeno score `1` exactly the
closed HOL universal-predicate event. This is the intended seam for arbitrary
capacities: they may enter the proof-theoretic endpoint layer only after
supplying this representation proof. -/
structure PredicateSugenoOneCalibration
    (T : ClosedTheorySet (WithParams Const))
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau) where
  fintype :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  measurable :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      MeasurableSpace (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  capacity :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      FuzzyCapacity (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  represents_forall :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      letI := fintype M
      letI := measurable M
      ((sugenoScoreInf (capacity M)
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ) = 1 ↔
        HenkinModel.models M.1
          (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)

/-- A calibrated capacity family yields a definable Sugeno endpoint cut.

This is the generic, non-laundering version of the counting-capacity cut below:
arbitrary capacities are allowed, but only through a calibration certificate
that identifies the endpoint event with a closed HOL formula. -/
noncomputable def predicateSugenoCalibratedCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := C.fintype M
      letI := C.measurable M
      ((sugenoScoreInf (C.capacity M)
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := C.fintype M
      letI := C.measurable M
      constructor
      · intro hModels
        have hEq :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 :=
          (C.represents_forall M).2 hModels
        change 1 ≤
          ((sugenoScoreInf (C.capacity M)
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ)
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) ≤ 1 :=
          unitInterval.le_one _
        have hEq :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact (C.represents_forall M).1 hEq }

/-- Normalized counting capacity supplies the first concrete Sugeno endpoint
calibration. -/
noncomputable def predicateSugenoCountingOneCalibration
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau)) :
    PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p where
  fintype := hObj
  measurable := hMeasurable
  capacity := fun M => by
    letI := hObj M
    letI := hMeasurable M
    exact FuzzyCapacity.countingCapacity
      (U := (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
  represents_forall := by
    intro M
    letI := hObj M
    letI := hNonempty M
    letI := hMeasurable M
    exact
      predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) M.1 tau p

/-- Counting-capacity Sugeno aggregation of a HOL-induced crisp profile is a
definable endpoint cut represented by the HOL universal predicate formula.

This is the first arbitrary-domain capacity/Sugeno consumer of the definable-cut
layer. It is intentionally restricted to normalized counting capacity: arbitrary
capacities do not make `capacity(extension) = 1` equivalent to full extension
without an additional calibration theorem. -/
noncomputable def predicateSugenoCountingCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((sugenoScoreInf
        (FuzzyCapacity.countingCapacity
          (U := (PredicateObject
            (Base := Base) (Const := WithParams Const) M.1 tau)))
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      letI := hNonempty M
      letI := hMeasurable M
      constructor
      · intro hModels
        have hEq :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 :=
          (predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
            (Base := Base) (Const := WithParams Const) M.1 tau p).2 hModels
        change 1 ≤
          ((sugenoScoreInf
            (FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau)))
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ)
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) ≤ 1 :=
          unitInterval.le_one _
        have hEq :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
            (Base := Base) (Const := WithParams Const) M.1 tau p).1 hEq }

/-! ## Cut-level saturated analogy transfer -/

/-- Canonical lower-endpoint transfer for saturated source-side analogy.

If the finite-vocabulary similarity cut for `p` and `q` is certainly saturated
over the extensional canonical family, and the full-inheritance cut from `q` to
`r` is certainly saturated, then the transferred full-inheritance cut from `p`
to `r` is certainly saturated as well. This is the credal/envelope-facing form
of the exact-threshold analogy-transfer theorem; it deliberately does not claim
soft similarity transfer below threshold `1`. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hQRLower :
      ((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hQR0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hQR0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  have hSimAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hSimLower
  have hQRAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cqr.threshold ≤ Cqr.score M :=
    (Cqr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hQRLower
  exact
    (Cpr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2 <|
      fun M => by
        letI := hObj M
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hSimAll M
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hSimLe hSimGe
        have hQRGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Cqr, predicateVocabularyFullInheritanceGeOneCut] using hQRAll M
        have hQRLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hQREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hQRLe hQRGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_source_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hpI M) (hqE M) (hqI M) (hrI M) hSimEq hQREq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm

/-- Canonical lower-endpoint transfer for saturated target-side analogy. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).extent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hPQLower :
      ((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hrE hqI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hrE hqI hSim0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  have hPQAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cpq.threshold ≤ Cpq.score M :=
    (Cpq.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hPQLower
  have hSimAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hSimLower
  exact
    (Cpr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2 <|
      fun M => by
        letI := hObj M
        have hPQGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Cpq, predicateVocabularyFullInheritanceGeOneCut] using hPQAll M
        have hPQLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hPQEq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hPQLe hPQGe
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hSimAll M
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hSimLe hSimGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_target_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hqI M) (hqE M) (hrE M) (hrI M) hPQEq hSimEq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm

/-- Negative example discipline: a formula cannot represent a threshold event
if it is true in some model where the threshold fails. -/
theorem no_cut_representation_of_true_formula_below_threshold
    {T : ClosedTheorySet (WithParams Const)}
    {score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ}
    {threshold : ℝ}
    {φ : ClosedFormula (WithParams Const)}
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T)
    (hModels : HenkinModel.models M.1 φ)
    (hBelow : ¬ threshold ≤ score M) :
    ¬ ∃ _hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ,
      ∀ N : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models N.1 φ ↔ threshold ≤ score N := by
  rintro ⟨_, hrepr⟩
  exact hBelow ((hrepr M).mp hModels)

/-- Negative example discipline: a formula cannot represent a threshold event
if it is false in some model where the threshold holds. -/
theorem no_cut_representation_of_false_formula_above_threshold
    {T : ClosedTheorySet (WithParams Const)}
    {score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ}
    {threshold : ℝ}
    {φ : ClosedFormula (WithParams Const)}
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T)
    (hNotModels : ¬ HenkinModel.models M.1 φ)
    (hAbove : threshold ≤ score M) :
    ¬ ∃ _hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ,
      ∀ N : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models N.1 φ ↔ threshold ≤ score N := by
  rintro ⟨_, hrepr⟩
  exact hNotModels ((hrepr M).mpr hAbove)

end Mettapedia.Logic.PLNHigherOrderHOLDefinableCuts
