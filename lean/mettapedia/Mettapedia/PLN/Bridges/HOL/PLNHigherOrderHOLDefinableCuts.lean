import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge

/-!
# Definable Numeric Cuts for Completeness-Tight HO-PLN

The formula-level completeness theorem is endpoint-tight over
`ExtensionalTheoryModel`. Numeric higher-order PLN quantities may inherit that
tightness only after their threshold events are represented by actual closed HOL
formulae. This file formalizes that seam without claiming that arbitrary
numeric consumers are already definable.
-/

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

/-! ## Cut transport and calibrated numeric readouts -/

/-- Positive affine rescaling preserves definable cuts.

This is the safe algebraic part of "general rational cuts": once a numeric
threshold event is represented by a closed HOL formula, changing units or
calibrating a displayed truth-value coordinate by `x ↦ a*x + b` with `0 < a`
keeps the same formula as the exact threshold event for the rescaled score. It
does not assert that an arbitrary numeric observable is definable. -/
def ExtensionalDefinableCut.posAffineRescale
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (a b : ℝ) (ha : 0 < a) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M => a * C.score M + b
    threshold := a * C.threshold + b
    formula := C.formula
    paramFree := C.paramFree
    represents_ge := by
      intro M
      constructor
      · intro hModels
        have h : C.threshold ≤ C.score M := (C.represents_ge M).mp hModels
        nlinarith
      · intro hGe
        apply (C.represents_ge M).mpr
        nlinarith }

@[simp]
theorem ExtensionalDefinableCut.posAffineRescale_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (a b : ℝ) (ha : 0 < a)
    (enum : Nat → Body Const)
    (henum : ∀ body : Body Const, ∃ n, enum n = body)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.posAffineRescale (Base := Base) (Const := Const) a b ha).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM =
      C.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM := rfl

/-- Boolean-valued endpoint cuts transport to every positive threshold at most
`1`.

This is the reusable non-laundering piece behind many PLN book-rule endpoint
certificates.  If a concrete consumer has already proved that threshold `1` is
represented by a closed HOL formula, and its displayed score is literally
Boolean-valued (`0` or `1`) on every canonical model, then the same formula also
represents `τ ≤ score` for any `0 < τ ≤ 1`.  The Boolean-valued hypothesis is
load-bearing: fractional counting/Sugeno scores do not get this theorem. -/
def ExtensionalDefinableCut.booleanPositiveThreshold
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (hThreshold : C.threshold = 1)
    (hBoolean : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      C.score M = 0 ∨ C.score M = 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := C.score
    threshold := τ
    formula := C.formula
    paramFree := C.paramFree
    represents_ge := by
      intro M
      constructor
      · intro hModels
        have hOne : (1 : ℝ) ≤ C.score M := by
          simpa [hThreshold] using (C.represents_ge M).mp hModels
        exact le_trans hτle hOne
      · intro hGe
        apply (C.represents_ge M).mpr
        rw [hThreshold]
        rcases hBoolean M with hZero | hOne
        · have hNot : ¬ τ ≤ C.score M := by
            simpa [hZero] using (not_le.mpr hτpos)
          exact False.elim (hNot hGe)
        · simp [hOne] }

@[simp]
theorem ExtensionalDefinableCut.booleanPositiveThreshold_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (hThreshold : C.threshold = 1)
    (hBoolean : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      C.score M = 0 ∨ C.score M = 1)
    (enum : Nat → Body Const)
    (henum : ∀ body : Body Const, ∃ n, enum n = body)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (C.booleanPositiveThreshold
      (Base := Base) (Const := Const) τ hτpos hτle hThreshold hBoolean).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM =
      C.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM := rfl

/-- Nonpositive thresholds for Boolean-valued scores are tautological cuts.

This is the boundary companion to `booleanPositiveThreshold`: when `τ ≤ 0`,
the event `τ ≤ score` is true for every Boolean-valued score.  The honest
representing HOL formula is therefore excluded middle for the original
representing formula, not the original formula itself. -/
noncomputable def ExtensionalDefinableCut.booleanNonpositiveThresholdTautology
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (τ : ℝ) (hτnonpos : τ ≤ 0)
    (hBoolean : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      C.score M = 0 ∨ C.score M = 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T := by
  classical
  exact
    { score := C.score
      threshold := τ
      formula := .or C.formula (.not C.formula)
      paramFree := by
        intro σ k
        exact NoConstOccurrence.or (C.paramFree σ k)
          (NoConstOccurrence.not (C.paramFree σ k))
      represents_ge := by
        intro M
        have hModelsTaut :
            HenkinModel.models M.1 (.or C.formula (.not C.formula)) := by
          by_cases hModels : HenkinModel.models M.1 C.formula
          · exact (HenkinModel.models_or M.1).mpr (Or.inl hModels)
          · exact (HenkinModel.models_or M.1).mpr
              (Or.inr ((HenkinModel.models_not M.1).mpr hModels))
        have hThreshold : τ ≤ C.score M := by
          rcases hBoolean M with hZero | hOne
          · simpa [hZero] using hτnonpos
          · simpa [hOne] using (le_trans hτnonpos zero_le_one)
        exact ⟨fun _ => hThreshold, fun _ => hModelsTaut⟩ }

/-- Conjunction closure for definable cuts.

If two numeric threshold events are already represented by closed HOL formulae,
their joint event is represented by HOL conjunction. The displayed score is the
minimum of the two signed margins, so threshold `0` is exactly simultaneous
satisfaction of both original cuts. -/
def ExtensionalDefinableCut.andCut
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M => min (C.score M - C.threshold) (D.score M - D.threshold)
    threshold := 0
    formula := .and C.formula D.formula
    paramFree := by
      intro σ k
      exact NoConstOccurrence.and (C.paramFree σ k) (D.paramFree σ k)
    represents_ge := by
      intro M
      constructor
      · intro hModels
        have hBoth := (HenkinModel.models_and M.1).mp hModels
        have hC : C.threshold ≤ C.score M := (C.represents_ge M).mp hBoth.1
        have hD : D.threshold ≤ D.score M := (D.represents_ge M).mp hBoth.2
        exact le_min (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)
      · intro hMin
        have hCdiff : 0 ≤ C.score M - C.threshold := le_trans hMin (min_le_left _ _)
        have hDdiff : 0 ≤ D.score M - D.threshold := le_trans hMin (min_le_right _ _)
        have hC : C.threshold ≤ C.score M := sub_nonneg.mp hCdiff
        have hD : D.threshold ≤ D.score M := sub_nonneg.mp hDdiff
        exact (HenkinModel.models_and M.1).mpr
          ⟨(C.represents_ge M).mpr hC, (D.represents_ge M).mpr hD⟩ }

/-- Disjunction closure for definable cuts.

If two numeric threshold events are already represented by closed HOL formulae,
their alternative event is represented by HOL disjunction. The displayed score
is the maximum of the two signed margins, so threshold `0` is exactly
satisfaction of at least one original cut. -/
def ExtensionalDefinableCut.orCut
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M => max (C.score M - C.threshold) (D.score M - D.threshold)
    threshold := 0
    formula := .or C.formula D.formula
    paramFree := by
      intro σ k
      exact NoConstOccurrence.or (C.paramFree σ k) (D.paramFree σ k)
    represents_ge := by
      intro M
      constructor
      · intro hModels
        have hEither := (HenkinModel.models_or M.1).mp hModels
        rcases hEither with hCmodels | hDmodels
        · have hC : C.threshold ≤ C.score M := (C.represents_ge M).mp hCmodels
          exact le_trans (sub_nonneg.mpr hC) (le_max_left _ _)
        · have hD : D.threshold ≤ D.score M := (D.represents_ge M).mp hDmodels
          exact le_trans (sub_nonneg.mpr hD) (le_max_right _ _)
      · intro hMax
        by_cases hCdiff : 0 ≤ C.score M - C.threshold
        · exact (HenkinModel.models_or M.1).mpr
            (Or.inl ((C.represents_ge M).mpr (sub_nonneg.mp hCdiff)))
        · have hDdiff : 0 ≤ D.score M - D.threshold := by
            by_contra hDneg
            have hCneg : C.score M - C.threshold < 0 := lt_of_not_ge hCdiff
            have hDneg' : D.score M - D.threshold < 0 := lt_of_not_ge hDneg
            have hMaxNeg :
                max (C.score M - C.threshold) (D.score M - D.threshold) < 0 :=
              max_lt hCneg hDneg'
            exact not_lt_of_ge hMax hMaxNeg
          exact (HenkinModel.models_or M.1).mpr
            (Or.inr ((D.represents_ge M).mpr (sub_nonneg.mp hDdiff))) }

/-- Complement closure for definable cuts.

The complement of a threshold event is represented by HOL negation.  Because
the complement of `t ≤ score` is strict failure, the score is an indicator for
the failed event rather than the signed margin `t - score`; this keeps equality
at the original threshold on the original side only. -/
noncomputable def ExtensionalDefinableCut.notCut
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M => if C.threshold ≤ C.score M then (0 : ℝ) else 1
    threshold := 1
    formula := .not C.formula
    paramFree := by
      intro σ k
      exact NoConstOccurrence.not (C.paramFree σ k)
    represents_ge := by
      intro M
      by_cases hGe : C.threshold ≤ C.score M
      · have hModels : HenkinModel.models M.1 C.formula :=
          (C.represents_ge M).mpr hGe
        simp [hGe, hModels]
      · have hNotModels : ¬ HenkinModel.models M.1 C.formula := by
          intro hModels
          exact hGe ((C.represents_ge M).mp hModels)
        simp [hGe, hNotModels] }

/-- Implication closure for definable cuts.

This is the rule-facing Boolean closure: once two threshold events have
definable certificates, the event "if the premise cut holds, then the
conclusion cut holds" is represented by HOL implication.  The displayed score is
a Boolean indicator of the material implication, not a new numeric rule
semantics. -/
noncomputable def ExtensionalDefinableCut.impCut
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      if C.threshold ≤ C.score M then
        if D.threshold ≤ D.score M then (1 : ℝ) else 0
      else 1
    threshold := 1
    formula := .imp C.formula D.formula
    paramFree := by
      intro σ k
      exact NoConstOccurrence.imp (C.paramFree σ k) (D.paramFree σ k)
    represents_ge := by
      intro M
      by_cases hC : C.threshold ≤ C.score M
      · have hCmodels : HenkinModel.models M.1 C.formula :=
          (C.represents_ge M).mpr hC
        by_cases hD : D.threshold ≤ D.score M
        · have hDmodels : HenkinModel.models M.1 D.formula :=
            (D.represents_ge M).mpr hD
          simp [hC, hD, hCmodels, hDmodels]
        · have hNotDmodels : ¬ HenkinModel.models M.1 D.formula := by
            intro hDmodels
            exact hD ((D.represents_ge M).mp hDmodels)
          simp [hC, hD, hCmodels, hNotDmodels]
      · have hNotCmodels : ¬ HenkinModel.models M.1 C.formula := by
          intro hCmodels
          exact hC ((C.represents_ge M).mp hCmodels)
        simp [hC, hNotCmodels] }

@[simp]
theorem ExtensionalDefinableCut.andCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (C.andCut (Base := Base) (Const := Const) D).threshold ≤
        (C.andCut (Base := Base) (Const := Const) D).score M ↔
      C.threshold ≤ C.score M ∧ D.threshold ≤ D.score M := by
  constructor
  · intro hMin
    have hCdiff : 0 ≤ C.score M - C.threshold :=
      le_trans hMin (min_le_left _ _)
    have hDdiff : 0 ≤ D.score M - D.threshold :=
      le_trans hMin (min_le_right _ _)
    exact ⟨sub_nonneg.mp hCdiff, sub_nonneg.mp hDdiff⟩
  · intro hBoth
    exact le_min (sub_nonneg.mpr hBoth.1) (sub_nonneg.mpr hBoth.2)

@[simp]
theorem ExtensionalDefinableCut.orCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (C.orCut (Base := Base) (Const := Const) D).threshold ≤
        (C.orCut (Base := Base) (Const := Const) D).score M ↔
      C.threshold ≤ C.score M ∨ D.threshold ≤ D.score M := by
  constructor
  · intro hMax
    by_cases hCdiff : 0 ≤ C.score M - C.threshold
    · exact Or.inl (sub_nonneg.mp hCdiff)
    · have hDdiff : 0 ≤ D.score M - D.threshold := by
        by_contra hDneg
        have hCneg : C.score M - C.threshold < 0 := lt_of_not_ge hCdiff
        have hDneg' : D.score M - D.threshold < 0 := lt_of_not_ge hDneg
        have hMaxNeg :
            max (C.score M - C.threshold) (D.score M - D.threshold) < 0 :=
          max_lt hCneg hDneg'
        exact not_lt_of_ge hMax hMaxNeg
      exact Or.inr (sub_nonneg.mp hDdiff)
  · intro hEither
    rcases hEither with hC | hD
    · exact le_trans (sub_nonneg.mpr hC) (le_max_left _ _)
    · exact le_trans (sub_nonneg.mpr hD) (le_max_right _ _)

@[simp]
theorem ExtensionalDefinableCut.notCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (C.notCut (Base := Base) (Const := Const)).threshold ≤
        (C.notCut (Base := Base) (Const := Const)).score M ↔
      ¬ C.threshold ≤ C.score M := by
  by_cases hGe : C.threshold ≤ C.score M <;>
    simp [ExtensionalDefinableCut.notCut, hGe]

@[simp]
theorem ExtensionalDefinableCut.impCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (C.impCut (Base := Base) (Const := Const) D).threshold ≤
        (C.impCut (Base := Base) (Const := Const) D).score M ↔
      (C.threshold ≤ C.score M → D.threshold ≤ D.score M) := by
  by_cases hC : C.threshold ≤ C.score M <;>
    by_cases hD : D.threshold ≤ D.score M <;>
      simp [ExtensionalDefinableCut.impCut, hC, hD]

/-- Lower endpoint package for conjunctive certified cuts: certainty of the
joint cut is exactly universal satisfaction of both original threshold events
over the canonical extensional theory-model class. -/
theorem ExtensionalDefinableCut.andCut_lower_eq_one_iff_forall_both_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.andCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M ∧ D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.lower_eq_one_iff_forall_ge]
  constructor
  · intro hAll M
    exact (C.andCut_ge_iff (Base := Base) (Const := Const) D M).mp (hAll M)
  · intro hAll M
    exact (C.andCut_ge_iff (Base := Base) (Const := Const) D M).mpr (hAll M)

/-- Lower endpoint package for disjunctive certified cuts: certainty of the
alternative cut is exactly universal satisfaction of at least one original
threshold event over the canonical extensional theory-model class. -/
theorem ExtensionalDefinableCut.orCut_lower_eq_one_iff_forall_either_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.orCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M ∨ D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.lower_eq_one_iff_forall_ge]
  constructor
  · intro hAll M
    exact (C.orCut_ge_iff (Base := Base) (Const := Const) D M).mp (hAll M)
  · intro hAll M
    exact (C.orCut_ge_iff (Base := Base) (Const := Const) D M).mpr (hAll M)

/-- Lower endpoint package for complement certified cuts: certainty of the
complement cut is exactly universal failure of the original threshold event. -/
theorem ExtensionalDefinableCut.notCut_lower_eq_one_iff_forall_not_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.notCut (Base := Base) (Const := Const)).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ C.threshold ≤ C.score M := by
  rw [ExtensionalDefinableCut.lower_eq_one_iff_forall_ge]
  constructor
  · intro hAll M
    exact (C.notCut_ge_iff (Base := Base) (Const := Const) M).mp (hAll M)
  · intro hAll M
    exact (C.notCut_ge_iff (Base := Base) (Const := Const) M).mpr (hAll M)

/-- Lower endpoint package for implication certified cuts: certainty of the
rule cut is exactly universal preservation of the conclusion threshold whenever
the premise threshold holds. -/
theorem ExtensionalDefinableCut.impCut_lower_eq_one_iff_forall_imp_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.impCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M → D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.lower_eq_one_iff_forall_ge]
  constructor
  · intro hAll M
    exact (C.impCut_ge_iff (Base := Base) (Const := Const) D M).mp (hAll M)
  · intro hAll M
    exact (C.impCut_ge_iff (Base := Base) (Const := Const) D M).mpr (hAll M)

/-- Upper endpoint package for conjunctive certified cuts: refutation of the
joint cut is exactly universal failure of simultaneous threshold satisfaction
over the canonical extensional theory-model class. -/
theorem ExtensionalDefinableCut.andCut_upper_eq_zero_iff_forall_not_both_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.andCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ (C.threshold ≤ C.score M ∧ D.threshold ≤ D.score M) := by
  rw [ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge]
  constructor
  · intro hAll M hBoth
    exact hAll M ((C.andCut_ge_iff (Base := Base) (Const := Const) D M).mpr hBoth)
  · intro hAll M hCut
    exact hAll M ((C.andCut_ge_iff (Base := Base) (Const := Const) D M).mp hCut)

/-- Upper endpoint package for disjunctive certified cuts: refutation of the
alternative cut is exactly universal failure of both original threshold events
over the canonical extensional theory-model class. -/
theorem ExtensionalDefinableCut.orCut_upper_eq_zero_iff_forall_not_either_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.orCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ (C.threshold ≤ C.score M ∨ D.threshold ≤ D.score M) := by
  rw [ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge]
  constructor
  · intro hAll M hEither
    exact hAll M ((C.orCut_ge_iff (Base := Base) (Const := Const) D M).mpr hEither)
  · intro hAll M hCut
    exact hAll M ((C.orCut_ge_iff (Base := Base) (Const := Const) D M).mp hCut)

/-- Upper endpoint package for complement certified cuts: refutation of the
complement cut is exactly universal satisfaction of the original threshold
event. -/
theorem ExtensionalDefinableCut.notCut_upper_eq_zero_iff_forall_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.notCut (Base := Base) (Const := Const)).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M := by
  rw [ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge]
  constructor
  · intro hAll M
    by_contra hFail
    exact hAll M ((C.notCut_ge_iff (Base := Base) (Const := Const) M).mpr hFail)
  · intro hAll M hNotCut
    exact (C.notCut_ge_iff (Base := Base) (Const := Const) M).mp hNotCut (hAll M)

/-- Upper endpoint package for implication certified cuts: refutation of the
rule cut is exactly universal counterexample behavior, i.e. the premise
threshold holds while the conclusion threshold fails in every model. -/
theorem ExtensionalDefinableCut.impCut_upper_eq_zero_iff_forall_counterexample_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.impCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M ∧ ¬ D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge]
  constructor
  · intro hAll M
    have hNotImp :
        ¬ (C.threshold ≤ C.score M → D.threshold ≤ D.score M) := by
      intro hImp
      exact hAll M
        ((C.impCut_ge_iff (Base := Base) (Const := Const) D M).mpr hImp)
    by_cases hC : C.threshold ≤ C.score M
    · refine ⟨hC, ?_⟩
      intro hD
      exact hNotImp (fun _ => hD)
    · exact False.elim (hNotImp (fun hC' => False.elim (hC hC')))
  · intro hAll M hCut
    have hImp :
        C.threshold ≤ C.score M → D.threshold ≤ D.score M :=
      (C.impCut_ge_iff (Base := Base) (Const := Const) D M).mp hCut
    exact (hAll M).2 (hImp (hAll M).1)

/-! ### Nonempty finite certified conjunctions -/

/-- Nonempty finite conjunction closure for certified cuts.

`allCut C Cs` folds an already-proven head cut with any finite list of
additional certified cuts. This is the multi-premise rule-gate version of
`andCut`: it gives rule families one certified threshold event for "all these
premises/side-conditions hold" without claiming that any premise's numeric
threshold is definable for free. -/
def ExtensionalDefinableCut.allCut
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    List (ExtensionalDefinableCut (Base := Base) (Const := Const) T) →
      ExtensionalDefinableCut (Base := Base) (Const := Const) T
  | [] => C
  | D :: Ds => (C.andCut (Base := Base) (Const := Const) D).allCut Ds

@[simp]
theorem ExtensionalDefinableCut.allCut_nil
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    C.allCut (Base := Base) (Const := Const) [] = C := rfl

@[simp]
theorem ExtensionalDefinableCut.allCut_cons
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Ds : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T)) :
    C.allCut (Base := Base) (Const := Const) (D :: Ds) =
      (C.andCut (Base := Base) (Const := Const) D).allCut Ds := rfl

/-- The nonempty finite conjunction cut is true in a model exactly when the
head cut and every tail cut's threshold event are true in that model. -/
@[simp]
theorem ExtensionalDefinableCut.allCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (C.allCut (Base := Base) (Const := Const) Cs).threshold ≤
        (C.allCut (Base := Base) (Const := Const) Cs).score M ↔
      C.threshold ≤ C.score M ∧
        ∀ D ∈ Cs, D.threshold ≤ D.score M := by
  induction Cs generalizing C with
  | nil =>
      simp [ExtensionalDefinableCut.allCut]
  | cons D Ds ih =>
      rw [ExtensionalDefinableCut.allCut_cons, ih]
      constructor
      · intro h
        rcases h with ⟨hCD, hTail⟩
        have hBoth :
            C.threshold ≤ C.score M ∧ D.threshold ≤ D.score M :=
          (C.andCut_ge_iff (Base := Base) (Const := Const) D M).mp hCD
        refine ⟨hBoth.1, ?_⟩
        intro E hE
        rcases List.mem_cons.mp hE with hEq | hMem
        · simpa [hEq] using hBoth.2
        · exact hTail E hMem
      · intro h
        refine ⟨?_, ?_⟩
        · exact
            (C.andCut_ge_iff (Base := Base) (Const := Const) D M).mpr
              ⟨h.1, h.2 D (by simp)⟩
        · intro E hE
          exact h.2 E (by simp [hE])

/-- Lower endpoint package for nonempty finite certified conjunctions:
certainty of the folded gate is exactly universal satisfaction of every
underlying certified threshold event. -/
theorem ExtensionalDefinableCut.allCut_lower_eq_one_iff_forall_all_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.allCut (Base := Base) (Const := Const) Cs).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M ∧
          ∀ D ∈ Cs, D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.lower_eq_one_iff_forall_ge]
  constructor
  · intro hAll M
    exact (C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mp (hAll M)
  · intro hAll M
    exact (C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mpr (hAll M)

/-- Upper endpoint package for nonempty finite certified conjunctions:
refutation of the folded gate is exactly universal failure of at least one
underlying threshold event. -/
theorem ExtensionalDefinableCut.allCut_upper_eq_zero_iff_forall_not_all_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ((C.allCut (Base := Base) (Const := Const) Cs).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ (C.threshold ≤ C.score M ∧
          ∀ D ∈ Cs, D.threshold ≤ D.score M) := by
  rw [ExtensionalDefinableCut.upper_eq_zero_iff_forall_not_ge]
  constructor
  · intro hAll M hCuts
    exact hAll M
      ((C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mpr hCuts)
  · intro hAll M hFold
    exact hAll M
      ((C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mp hFold)

/-- Lower endpoint package for a finite certified rule gate: certainty of the
material implication from `allCut C Cs` to `D` is exactly universal preservation
of the conclusion threshold whenever every certified premise threshold holds.

This is the multi-premise rule-family surface: it composes already-certified
threshold events, but it does not certify any numeric premise by itself. -/
theorem ExtensionalDefinableCut.allCut_impCut_lower_eq_one_iff_forall_all_imp_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (((C.allCut (Base := Base) (Const := Const) Cs).impCut
        (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        (C.threshold ≤ C.score M ∧
          ∀ E ∈ Cs, E.threshold ≤ E.score M) →
        D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.impCut_lower_eq_one_iff_forall_imp_ge]
  constructor
  · intro hAll M hPremises
    exact hAll M
      ((C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mpr hPremises)
  · intro hAll M hGate
    exact hAll M
      ((C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mp hGate)

/-- Upper endpoint package for a finite certified rule gate: refuting the
material implication from `allCut C Cs` to `D` is exactly universal
counterexample behavior, where every certified premise threshold holds and the
conclusion threshold fails in every canonical model. -/
theorem ExtensionalDefinableCut.allCut_impCut_upper_eq_zero_iff_forall_all_counterexample_ge
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (((C.allCut (Base := Base) (Const := Const) Cs).impCut
        (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 ↔
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        (C.threshold ≤ C.score M ∧
          ∀ E ∈ Cs, E.threshold ≤ E.score M) ∧
        ¬ D.threshold ≤ D.score M := by
  rw [ExtensionalDefinableCut.impCut_upper_eq_zero_iff_forall_counterexample_ge]
  constructor
  · intro hAll M
    exact
      ⟨(C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mp (hAll M).1,
        (hAll M).2⟩
  · intro hAll M
    exact
      ⟨(C.allCut_ge_iff (Base := Base) (Const := Const) Cs M).mpr (hAll M).1,
        (hAll M).2⟩

/-- Certified-cut modus ponens.

If the implication cut `C -> D` is certain over the canonical extensional model
family, and the premise cut `C` is certain, then the conclusion cut `D` is
certain. This is the generic rule consumer for `impCut`; concrete rule families
should still prove their own implication cut rather than assume it. -/
theorem ExtensionalDefinableCut.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hRule :
      ((C.impCut (Base := Base) (Const := Const) D).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hPrem :
      (C.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    (D.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  have hRuleAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M → D.threshold ≤ D.score M :=
    (C.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) D enum henum hCons hT0 hEM).1 hRule
  have hPremAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M :=
    (C.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hPrem
  exact
    (D.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => hRuleAll M (hPremAll M))

/-- Multi-premise certified-cut modus ponens.

If a finite certified premise gate is certain and its implication to a
conclusion cut is certain, then the conclusion cut is certain. This is only a
consumer of certified cuts; concrete PLN rules must still discharge the
finite-gate implication cut. -/
theorem ExtensionalDefinableCut.lower_eq_one_of_allCut_impCut_lower_eq_one_of_allCut_lower_eq_one
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (Cs : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hRule :
      (((C.allCut (Base := Base) (Const := Const) Cs).impCut
          (Base := Base) (Const := Const) D).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hPremises :
      ((C.allCut (Base := Base) (Const := Const) Cs).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    (D.intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  exact
    (C.allCut (Base := Base) (Const := Const) Cs)
      |>.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
        (Base := Base) (Const := Const) D enum henum hCons hT0 hEM hRule hPremises

/-- Certified-cut modus tollens.

If the implication cut `C -> D` is certain and the complement of `D` is certain,
then the complement of `C` is certain.  This is a rule-facing negative
consumer: it reuses the already-certified implication and complement cuts
instead of defining a separate contrapositive score. -/
theorem ExtensionalDefinableCut.notCut_lower_eq_one_of_impCut_lower_eq_one_of_notCut_lower_eq_one
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hRule :
      ((C.impCut (Base := Base) (Const := Const) D).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hNotConc :
      ((D.notCut (Base := Base) (Const := Const)).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((C.notCut (Base := Base) (Const := Const)).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  have hRuleAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M → D.threshold ≤ D.score M :=
    (C.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) D enum henum hCons hT0 hEM).1 hRule
  have hNotConcAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ D.threshold ≤ D.score M :=
    (D.notCut_lower_eq_one_iff_forall_not_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hNotConc
  exact
    (C.notCut_lower_eq_one_iff_forall_not_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M hPrem => hNotConcAll M (hRuleAll M hPrem))

/-- A certified implication cut is refuted when the premise cut is certain and
the conclusion cut is refuted.

This is the endpoint form of the familiar counterexample pattern: every
canonical model satisfies the premise threshold and fails the conclusion
threshold, so every canonical model refutes the material rule cut. -/
theorem ExtensionalDefinableCut.impCut_upper_eq_zero_of_lower_eq_one_of_upper_eq_zero
    {T : ClosedTheorySet (WithParams Const)}
    (C D : ExtensionalDefinableCut (Base := Base) (Const := Const) T)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hPrem :
      (C.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hConcRefuted :
      (D.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0) :
    ((C.impCut (Base := Base) (Const := Const) D).intervalOfConsistent
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).upper = 0 := by
  have hPremAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        C.threshold ≤ C.score M :=
    (C.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hPrem
  have hConcRefutedAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ¬ D.threshold ≤ D.score M :=
    (D.upper_eq_zero_iff_forall_not_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hConcRefuted
  exact
    (C.impCut_upper_eq_zero_iff_forall_counterexample_ge
      (Base := Base) (Const := Const) D enum henum hCons hT0 hEM).2
      (fun M => ⟨hPremAll M, hConcRefutedAll M⟩)

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

/-- Concrete non-`1` threshold example: the indicator score of a closed formula
is definably cut by the same formula at any positive threshold at most `1`.

This is a genuine arbitrary-threshold foothold for the rational-cut layer.  The
strict positivity hypothesis is load-bearing: at threshold `0`, the indicator
event is trivial rather than equivalent to the formula. -/
noncomputable def formulaIndicatorPositiveThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T := by
  classical
  exact
    { score := fun M =>
        if HenkinModel.models M.1 φ then (1 : ℝ) else 0
      threshold := τ
      formula := φ
      paramFree := hφ0
      represents_ge := by
        intro M
        by_cases h : HenkinModel.models M.1 φ
        · simp [h, hτle]
        · have hτnotle0 : ¬ τ ≤ (0 : ℝ) := not_le.mpr hτpos
          simp [h, hτnotle0] }

/-- The positive-threshold indicator cut has the same formula-level credal
interval as the endpoint-`1` indicator cut, because both are represented by
the same closed HOL formula. -/
theorem formulaIndicatorPositiveThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM =
      ExtensionalDefinableCut.intervalOfConsistent
        (Base := Base) (Const := Const)
        (formulaIndicatorGeOneCut (T := T) φ hφ0)
        enum henum hCons hT0 hEM := rfl

/-- Endpoint tightness for positive-threshold Boolean indicator cuts:
lower endpoint `1` is exactly provability of the represented formula. -/
theorem formulaIndicatorPositiveThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T φ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for positive-threshold Boolean indicator cuts:
upper endpoint `0` is exactly provability of the negated represented formula. -/
theorem formulaIndicatorPositiveThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not φ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for positive-threshold Boolean indicator cuts: the
interval collapses exactly when the theory decides the represented formula. -/
theorem formulaIndicatorPositiveThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτpos : 0 < τ) (hτle : τ ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T φ ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not φ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut (T := T) φ hφ0 τ hτpos hτle)
      enum henum hCons hT0 hEM

/-- Boundary certificate for Boolean indicators at nonpositive thresholds.

If `τ ≤ 0`, the event `τ ≤ 1_{φ}` is true in every model.  The honest
representing formula is therefore the excluded-middle tautology `φ ∨ ¬φ`, not
`φ` itself. -/
noncomputable def formulaIndicatorNonpositiveThresholdTautologyCut
    {T : ClosedTheorySet (WithParams Const)}
    (φ : ClosedFormula (WithParams Const))
    (hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ)
    (τ : ℝ) (hτnonpos : τ ≤ 0) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T := by
  classical
  exact
    { score := fun M =>
        if HenkinModel.models M.1 φ then (1 : ℝ) else 0
      threshold := τ
      formula := .or φ (.not φ)
      paramFree := by
        intro σ k
        exact NoConstOccurrence.or (hφ0 σ k) (NoConstOccurrence.not (hφ0 σ k))
      represents_ge := by
        intro M
        have hModelsTaut :
            HenkinModel.models M.1 (.or φ (.not φ)) := by
          by_cases hφ : HenkinModel.models M.1 φ
          · exact (HenkinModel.models_or M.1).mpr (Or.inl hφ)
          · exact (HenkinModel.models_or M.1).mpr
              (Or.inr ((HenkinModel.models_not M.1).mpr hφ))
        have hThreshold :
            τ ≤ (if HenkinModel.models M.1 φ then (1 : ℝ) else 0) := by
          by_cases hφ : HenkinModel.models M.1 φ
          · simpa [hφ] using (le_trans hτnonpos zero_le_one)
          · simpa [hφ] using hτnonpos
        exact ⟨fun _ => hThreshold, fun _ => hModelsTaut⟩ }

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

/-- Positive-threshold version of the strict finite-QFM `ForAll` endpoint cut.

The displayed QFM acceptance score here is Boolean-valued, so the general
Boolean-threshold transport applies.  This does not extend to fractional
near-one/counting scores without a separate threshold formula. -/
noncomputable def predicateFuzzyForAllCrispEndpointPositiveThresholdCut
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyForAllCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanPositiveThreshold
    (Base := Base) (Const := Const) theta htheta_pos htheta_le rfl
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyForAllHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-- The positive-threshold finite-QFM `ForAll` acceptance cut has exactly the
same formula-level credal interval as the endpoint-`1` acceptance cut.

The score threshold changes, but the already-proven Boolean transport keeps the
representing HOL formula fixed. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_intervalOfConsistent
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM =
      ExtensionalDefinableCut.intervalOfConsistent
        (Base := Base) (Const := Const)
        (predicateFuzzyForAllCrispEndpointGeOneCut
          (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0)
        enum henum hCons hT0 hEM := rfl

/-- Endpoint tightness for positive-threshold finite-QFM `ForAll`
acceptance: lower endpoint `1` is exactly provability of the HOL universal
predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for positive-threshold finite-QFM `ForAll`
acceptance: upper endpoint `0` is exactly provability of the negated HOL
universal predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for positive-threshold finite-QFM `ForAll`
acceptance: the interval collapses exactly when the theory decides the HOL
universal predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Nonpositive-threshold boundary for the strict finite-QFM `ForAll`
acceptance score.

Since the acceptance score is Boolean-valued, thresholds `τ ≤ 0` are always
satisfied.  The representing formula is therefore a tautology over the HOL
universal-predicate formula. -/
noncomputable def predicateFuzzyForAllCrispEndpointNonpositiveThresholdTautologyCut
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_nonpos : theta ≤ 0) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyForAllCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanNonpositiveThresholdTautology
    (Base := Base) (Const := Const) theta htheta_nonpos
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyForAllHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

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

/-- Positive-threshold version of the strict finite-QFM `ThereExists`
acceptance cut.

As with the `ForAll` acceptance cut, this applies only to the Boolean endpoint
acceptance score.  It does not claim that arbitrary sub-endpoint QFM mass
thresholds are already HOL-definable. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyThereExistsCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanPositiveThreshold
    (Base := Base) (Const := Const) theta htheta_pos htheta_le rfl
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyThereExistsHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-- The positive-threshold finite-QFM `ThereExists` acceptance cut has exactly
the same formula-level credal interval as the endpoint-`1` acceptance cut.

At this strict endpoint `ThereExists` is still the PLN book's no-near-zero
acceptance predicate over a crisp profile, so the shared representing formula
is the HOL universal predicate formula. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_intervalOfConsistent
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM =
      ExtensionalDefinableCut.intervalOfConsistent
        (Base := Base) (Const := Const)
        (predicateFuzzyThereExistsCrispEndpointGeOneCut
          (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0)
        enum henum hCons hT0 hEM := rfl

/-- Endpoint tightness for positive-threshold finite-QFM `ThereExists`
acceptance: lower endpoint `1` is exactly provability of the HOL universal
predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for positive-threshold finite-QFM `ThereExists`
acceptance: upper endpoint `0` is exactly provability of the negated HOL
universal predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for positive-threshold finite-QFM `ThereExists`
acceptance: the interval collapses exactly when the theory decides the HOL
universal predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Nonpositive-threshold boundary for the strict finite-QFM `ThereExists`
acceptance score. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointNonpositiveThresholdTautologyCut
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_nonpos : theta ≤ 0) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyThereExistsCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanNonpositiveThresholdTautology
    (Base := Base) (Const := Const) theta htheta_nonpos
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyThereExistsHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-! ## Fractional counting-capacity cut instances -/

/-- A nonempty subset of a finite carrier has normalized counting capacity at
least `1 / N` when the carrier has cardinality at most `N`.

This is the reusable finite-counting fact behind guarded fractional QFM cuts.
The cardinality bound is not cosmetic: nonemptiness alone gives only
`1 / |U|`, so no fixed positive threshold can be uniform over arbitrarily large
finite carriers. -/
theorem FuzzyCapacity.countingCapacity_ge_one_div_of_nonempty_of_card_le
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U ≤ N) (hA : A.Nonempty) :
    (1 : ℝ) / (N : ℝ) ≤
      ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) := by
  classical
  have hUNonempty : Nonempty U := ⟨hA.some⟩
  have hUposNat : 0 < Fintype.card U :=
    Fintype.card_pos_iff.mpr hUNonempty
  have hAposNat : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr ⟨⟨hA.some, hA.some_mem⟩⟩
  have hAgeNat : 1 ≤ Fintype.card A := Nat.succ_le_of_lt hAposNat
  have hAge : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast hAgeNat
  have hUleN : (Fintype.card U : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hCard
  have hUpos : 0 < (Fintype.card U : ℝ) := by
    exact_mod_cast hUposNat
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hU_ne : (Fintype.card U : ℝ) ≠ 0 := ne_of_gt hUpos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  change (1 : ℝ) / (N : ℝ) ≤
    ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ)
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = Fintype.card A := by
    simp
  rw [hFilterCard]
  rw [← one_div (N : ℝ)]
  change (1 : ℝ) / (N : ℝ) ≤
    (Fintype.card A : ℝ) / (Fintype.card U : ℝ)
  field_simp [hN_ne, hU_ne]
  nlinarith [hAge, hUleN, hNposR]

/-- On a finite carrier whose cardinality is exactly `N`, the normalized
counting-capacity threshold `k / N` is equivalent to the subset having at
least `k` elements.

This is the exact-denominator arithmetic needed for higher rational
cardinality cuts.  With only an upper bound on the carrier size, the reverse
direction is false: a smaller carrier can make a smaller witness set occupy a
larger fraction. -/
theorem FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (k N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    (k : ℝ) / (N : ℝ) ≤
        ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ↔
      k ≤ A.ncard := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  change (k : ℝ) / (N : ℝ) ≤
    ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) ↔
      k ≤ A.ncard
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hGe
    have hCast : (k : ℝ) ≤ (A.ncard : ℝ) := by
      field_simp [hN_ne] at hGe
      simpa using hGe
    exact_mod_cast hCast
  · intro hk
    have hCast : (k : ℝ) ≤ (A.ncard : ℝ) := by
      exact_mod_cast hk
    field_simp [hN_ne]
    simpa using hCast

/-- Constants absent from the predicate remain absent from the universal
predicate sentence. -/
theorem noConstOccurrence_predicateForAllFormula
    {τ : Ty Base} {c : Const τ}
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpc : NoConstOccurrence c p) :
    NoConstOccurrence c
      (predicateForAllFormula (Base := Base) (Const := Const) σ p) := by
  exact NoConstOccurrence.all
    (NoConstOccurrence.app
      (noConstOccurrence_rename
        (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) p hpc)
      NoConstOccurrence.var)

/-- In an exact finite predicate-object carrier of cardinality `N`, the HOL
universal predicate formula represents the saturated cardinality event
`N ≤ ncard(ext p)`.

This is the `k = N` companion to the existence / at-least-two / at-least-three
cardinality formulae used below. -/
theorem models_predicateForAllFormula_iff_card_le_ncard_extension_of_card_eq
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (N : Nat)
    (hCard :
      Fintype.card (PredicateObject (Base := Base) (Const := Const) M σ) = N) :
    HenkinModel.models M
        (predicateForAllFormula (Base := Base) (Const := Const) σ p) ↔
      N ≤
        (predicateExtension
          (Base := Base) (Const := Const) M σ p).ncard := by
  rw [models_predicateForAllFormula_iff]
  constructor
  · intro hAll
    have hExtEq :
        predicateExtension (Base := Base) (Const := Const) M σ p = Set.univ := by
      ext x
      constructor
      · intro _; simp
      · intro _
        exact hAll x
    rw [hExtEq, Set.ncard_univ, Nat.card_eq_fintype_card, hCard]
  · intro hN x
    have hNatCard :
        Nat.card (PredicateObject (Base := Base) (Const := Const) M σ) = N := by
      rw [Nat.card_eq_fintype_card, hCard]
    have hExtLe :
        (predicateExtension (Base := Base) (Const := Const) M σ p).ncard ≤ N := by
      calc
        (predicateExtension (Base := Base) (Const := Const) M σ p).ncard ≤
            Set.univ.ncard :=
          Set.ncard_le_ncard (by intro y _; simp) (Set.toFinite Set.univ)
        _ = Nat.card (PredicateObject (Base := Base) (Const := Const) M σ) := by
          rw [Set.ncard_univ]
        _ = N := hNatCard
    have hExtCard :
        (predicateExtension (Base := Base) (Const := Const) M σ p).ncard = N := by
      omega
    by_contra hx
    have hComplNonempty :
        ((predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ).Nonempty :=
      ⟨x, by simpa [predicateExtension] using hx⟩
    have hComplPos :
        0 <
          ((predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ).ncard :=
      (Set.ncard_pos).2 hComplNonempty
    have hSum :=
      Set.ncard_add_ncard_compl
        (predicateExtension (Base := Base) (Const := Const) M σ p)
    rw [hExtCard, hNatCard] at hSum
    omega

/-- Exact-denominator finite-QFM `ForAll` threshold cut for HOL-induced crisp
profiles under normalized counting capacity.

Unlike the Boolean endpoint transport above, this is a genuine fractional
threshold certificate.  The guards are load-bearing: `ε = 0`, `PCL = k / N`,
an exact carrier-size equation, and a param-free HOL formula `χ` representing
`k ≤ ncard (ext p)` over every canonical completion. -/
noncomputable def predicateFuzzyForAllCountingCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      nearOneFraction params
        (predicateCrispProfile
          (Base := Base) (Const := WithParams Const) M.1 σ p)
    threshold := params.PCL
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      have hNearEq :
          nearOneFraction params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) =
            (((FuzzyCapacity.countingCapacity
              (U := PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 σ))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 σ p) :
              unitInterval) : ℝ) := by
        calc
          nearOneFraction params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) =
              (nearOneMassInf params.toInf
                (FuzzyCapacity.countingCapacity
                  (U := PredicateObject
                    (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateCrispProfileInf
                  (Base := Base) (Const := WithParams Const) M.1 σ p) :
                ℝ) := by
                symm
                exact
                  predicateNearOneMassInf_counting_eq_nearOneFraction
                    (Base := Base) (Const := WithParams Const) M.1 σ params p
          _ =
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 σ p) :
                unitInterval) : ℝ) := by
                rw [predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
                  (Base := Base) (Const := WithParams Const) M.1 σ
                  params.toInf (by simpa [FuzzyQuantifierParams.toInf] using hε0)
                  (FuzzyCapacity.countingCapacity
                    (U := PredicateObject
                      (Base := Base) (Const := WithParams Const) M.1 σ)) p]
      constructor
      · intro hModels
        have hCount : k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard :=
          (hχRep M).1 hModels
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 σ p) :
                unitInterval) : ℝ) :=
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)
            k N hNpos (hCardEq M)).2 hCount
        simpa [hPCL, hNearEq] using hCap
      · intro hGe
        apply (hχRep M).2
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 σ p) :
                unitInterval) : ℝ) := by
          simpa [hPCL, hNearEq] using hGe
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)
            k N hNpos (hCardEq M)).1 hCap }

/-- The finite-QFM `ForAll` exact-denominator threshold cut reads out through
the existing HOL interval for its supplied cardinality-threshold formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for the generic exact-denominator finite-QFM `ForAll`
cardinality-threshold cut: lower endpoint `1` is exactly provability of the
supplied HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the generic exact-denominator finite-QFM `ForAll`
cardinality-threshold cut: upper endpoint `0` is exactly provability of the
negated supplied HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the generic exact-denominator finite-QFM
`ForAll` cardinality-threshold cut: lower endpoint `0` is exactly
non-provability of the supplied HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the generic exact-denominator finite-QFM
`ForAll` cardinality-threshold cut: upper endpoint `1` is exactly
non-provability of the negated supplied HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the generic exact-denominator finite-QFM `ForAll`
cardinality-threshold cut: the interval collapses exactly when the theory
decides the supplied HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- On a finite carrier whose cardinality is exactly `N`, a rational threshold
for the complement of normalized counting capacity is equivalent to a finite
upper-cardinality event.

The event is stated as `A.ncard + k ≤ N`, rather than with Nat subtraction, so
the out-of-range case `k > N` remains honest: the numeric threshold
`k / N ≤ 1 - countingCapacity(A)` is then false in every model. -/
theorem FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (k N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    (k : ℝ) / (N : ℝ) ≤
        1 - ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ↔
      A.ncard + k ≤ N := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  change (k : ℝ) / (N : ℝ) ≤
    1 - ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) ↔
      A.ncard + k ≤ N
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hGe
    have hCast : (A.ncard : ℝ) + (k : ℝ) ≤ (N : ℝ) := by
      field_simp [hN_ne] at hGe
      nlinarith
    exact_mod_cast hCast
  · intro hk
    have hCast : (A.ncard : ℝ) + (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hk
    field_simp [hN_ne]
    nlinarith

/-- On a finite carrier whose cardinality is exactly `N`, bounding the
complement cardinality by `Aᶜ.ncard + k ≤ N` is exactly the same as asking
`A` itself to contain at least `k` elements. -/
theorem Set.ncard_compl_add_le_iff_le_ncard_of_card_eq
    {U : Type u} [Fintype U] (A : Set U) (k N : Nat)
    (hCard : Fintype.card U = N) :
    Aᶜ.ncard + k ≤ N ↔ k ≤ A.ncard := by
  classical
  have hSum : Aᶜ.ncard + A.ncard = N := by
    have h0 := Set.ncard_add_ncard_compl Aᶜ
    simpa [compl_compl, hCard] using h0
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Exact-denominator finite-QFM `ThereExists` threshold cut for HOL-induced
crisp profiles under normalized counting capacity.

This represents the PLN book's QFM existential mass test
`PCL ≤ 1 - nearZeroFraction`, not ordinary HOL existential quantification.
Under `ε = 0`, exact denominator `PCL = k / N`, and an exact carrier-size
equation, that mass test is represented by the same cardinality-threshold HOL
formula used by the finite-QFM `ForAll` cut: `k ≤ ncard (ext p)`. -/
noncomputable def predicateFuzzyThereExistsCountingCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      1 - nearZeroFraction params
        (predicateCrispProfile
          (Base := Base) (Const := WithParams Const) M.1 σ p)
    threshold := params.PCL
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      have hNearEq :
          nearZeroFraction params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) =
            (((FuzzyCapacity.countingCapacity
              (U := PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 σ))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ :
              unitInterval) : ℝ) := by
        calc
          nearZeroFraction params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) =
              (nearZeroMassInf params.toInf
                (FuzzyCapacity.countingCapacity
                  (U := PredicateObject
                    (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateCrispProfileInf
                  (Base := Base) (Const := WithParams Const) M.1 σ p) :
                ℝ) := by
                symm
                exact
                  predicateNearZeroMassInf_counting_eq_nearZeroFraction
                    (Base := Base) (Const := WithParams Const) M.1 σ params p
          _ =
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 σ))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ :
                unitInterval) : ℝ) := by
                rw [predicateNearZeroMassInf_eq_capacity_compl_extension_of_epsilon_zero
                  (Base := Base) (Const := WithParams Const) M.1 σ
                  params.toInf (by simpa [FuzzyQuantifierParams.toInf] using hε0)
                  (FuzzyCapacity.countingCapacity
                    (U := PredicateObject
                      (Base := Base) (Const := WithParams Const) M.1 σ)) p]
      constructor
      · intro hModels
        have hCount : k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard :=
          (hχRep M).1 hModels
        have hComplCount :
            ((predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ).ncard +
                k ≤ N :=
          (Set.ncard_compl_add_le_iff_le_ncard_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)
            k N (hCardEq M)).2 hCount
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              1 -
                (((FuzzyCapacity.countingCapacity
                  (U := PredicateObject
                    (Base := Base) (Const := WithParams Const) M.1 σ))
                  (predicateExtension
                    (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ :
                  unitInterval) : ℝ) :=
          (FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            ((predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ)
            k N hNpos (hCardEq M)).2 hComplCount
        simpa [hPCL, hNearEq] using hCap
      · intro hGe
        apply (hχRep M).2
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              1 -
                (((FuzzyCapacity.countingCapacity
                  (U := PredicateObject
                    (Base := Base) (Const := WithParams Const) M.1 σ))
                  (predicateExtension
                    (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ :
                  unitInterval) : ℝ) := by
          simpa [hPCL, hNearEq] using hGe
        have hComplCount :
            ((predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ).ncard +
                k ≤ N :=
          (FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            ((predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)ᶜ)
            k N hNpos (hCardEq M)).1 hCap
        exact
          (Set.ncard_compl_add_le_iff_le_ncard_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 σ)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p)
            k N (hCardEq M)).1 hComplCount }

/-- The finite-QFM `ThereExists` exact-denominator threshold cut reads out
through the existing HOL interval for its supplied cardinality-threshold
formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for the generic exact-denominator finite-QFM
`ThereExists` cardinality-threshold cut: lower endpoint `1` is exactly
provability of the supplied HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ForAll` threshold cut for the HOL
existence formula `∃ x, p x`.

This specializes the generic counting-cardinality QFM cut at `k = 1` with the
already-proven representation theorem for ordinary HOL existence. Unlike the
base-type `at least two` / `at least three` cuts, this works at every HOL type
because it does not compare objects by equality. -/
noncomputable def predicateFuzzyForAllCountingExistsExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyForAllCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    σ params p
    (predicateExistsFormula (Base := Base) (Const := WithParams Const) σ p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) σ p (hp0 ρ i))
    hObj hMeasurable hε0 1 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 σ p)

/-- The concrete HOL-existence finite-QFM `ForAll` cut reads out through the
existing HOL interval for `∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) σ p) := rfl

/-- Endpoint tightness for the HOL-existence finite-QFM `ForAll` cut: lower
endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-existence finite-QFM `ForAll` cut: upper
endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-existence finite-QFM `ForAll`
cut: lower endpoint `0` is exactly non-provability of `∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  simpa [predicateFuzzyForAllCountingExistsExactThresholdCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-existence finite-QFM `ForAll`
cut: upper endpoint `1` is exactly non-provability of `¬ ∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  simpa [predicateFuzzyForAllCountingExistsExactThresholdCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-existence finite-QFM `ForAll` cut: the
interval collapses exactly when the theory decides `∃ x, p x`. -/
theorem predicateFuzzyForAllCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the generic exact-denominator finite-QFM
`ThereExists` cardinality-threshold cut: upper endpoint `0` is exactly
provability of the negated supplied HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the generic exact-denominator finite-QFM
`ThereExists` cardinality-threshold cut: lower endpoint `0` is exactly
non-provability of the supplied HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the generic exact-denominator finite-QFM
`ThereExists` cardinality-threshold cut: upper endpoint `1` is exactly
non-provability of the negated supplied HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the generic exact-denominator finite-QFM
`ThereExists` cardinality-threshold cut: the interval collapses exactly when
the theory decides the supplied HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (k N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (k : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 σ p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p χ hχ0 hObj hMeasurable hε0 k N hNpos hPCL hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ThereExists` threshold cut for the
HOL existence formula `∃ x, p x`.

This is the QFM mass test `PCL ≤ 1 - nearZeroFraction`, specialized at
`PCL = 1 / N`; it is represented by ordinary HOL existence only under the
explicit crisp exact-denominator guards. -/
noncomputable def predicateFuzzyThereExistsCountingExistsExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    σ params p
    (predicateExistsFormula (Base := Base) (Const := WithParams Const) σ p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) σ p (hp0 ρ i))
    hObj hMeasurable hε0 1 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 σ p)

/-- The concrete HOL-existence finite-QFM `ThereExists` cut reads out through
the existing HOL interval for `∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) σ p) := rfl

/-- Endpoint tightness for the HOL-existence finite-QFM `ThereExists` cut:
lower endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-existence finite-QFM `ThereExists` cut:
upper endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-existence finite-QFM
`ThereExists` cut: lower endpoint `0` is exactly non-provability of
`∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  simpa [predicateFuzzyThereExistsCountingExistsExactThresholdCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-existence finite-QFM
`ThereExists` cut: upper endpoint `1` is exactly non-provability of
`¬ ∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  simpa [predicateFuzzyThereExistsCountingExistsExactThresholdCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-existence finite-QFM `ThereExists` cut:
the interval collapses exactly when the theory decides `∃ x, p x`. -/
theorem predicateFuzzyThereExistsCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = ((1 : Nat) : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ForAll` threshold cut for the HOL
universal formula `∀ x, p x`.

This specializes the generic counting-cardinality QFM cut at `k = N` with the
exact-carrier representation theorem for ordinary HOL universal truth. -/
noncomputable def predicateFuzzyForAllCountingUniversalExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyForAllCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    σ params p
    (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)
    (fun ρ i =>
      noConstOccurrence_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) σ p (hp0 ρ i))
    hObj hMeasurable hε0 N N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateForAllFormula_iff_card_le_ncard_extension_of_card_eq
          (Base := Base) (Const := WithParams Const) M.1 σ p N (hCardEq M))

/-- The concrete HOL-universal finite-QFM `ForAll` cut reads out through the
existing HOL interval for `∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) σ p) := rfl

/-- Endpoint tightness for the HOL-universal finite-QFM `ForAll` cut: lower
endpoint `1` is exactly provability of `∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-universal finite-QFM `ForAll` cut: upper
endpoint `0` is exactly provability of `¬ ∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-universal finite-QFM `ForAll`
cut: lower endpoint `0` is exactly non-provability of `∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  simpa [predicateFuzzyForAllCountingUniversalExactThresholdCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-universal finite-QFM `ForAll`
cut: upper endpoint `1` is exactly non-provability of `¬ ∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  simpa [predicateFuzzyForAllCountingUniversalExactThresholdCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-universal finite-QFM `ForAll` cut: the
interval collapses exactly when the theory decides `∀ x, p x`. -/
theorem predicateFuzzyForAllCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ThereExists` threshold cut for the
HOL universal formula `∀ x, p x`.

At `PCL = N / N`, the exact-denominator mass test is represented by universal
truth under the explicit exact-carrier guards. -/
noncomputable def predicateFuzzyThereExistsCountingUniversalExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    σ params p
    (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)
    (fun ρ i =>
      noConstOccurrence_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) σ p (hp0 ρ i))
    hObj hMeasurable hε0 N N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateForAllFormula_iff_card_le_ncard_extension_of_card_eq
          (Base := Base) (Const := WithParams Const) M.1 σ p N (hCardEq M))

/-- The concrete HOL-universal finite-QFM `ThereExists` cut reads out through
the existing HOL interval for `∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) σ p) := rfl

/-- Endpoint tightness for the HOL-universal finite-QFM `ThereExists` cut:
lower endpoint `1` is exactly provability of `∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-universal finite-QFM `ThereExists` cut:
upper endpoint `0` is exactly provability of `¬ ∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-universal finite-QFM
`ThereExists` cut: lower endpoint `0` is exactly non-provability of
`∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) := by
  simpa [predicateFuzzyThereExistsCountingUniversalExactThresholdCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-universal finite-QFM
`ThereExists` cut: upper endpoint `1` is exactly non-provability of
`¬ ∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  simpa [predicateFuzzyThereExistsCountingUniversalExactThresholdCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-universal finite-QFM `ThereExists` cut:
the interval collapses exactly when the theory decides `∀ x, p x`. -/
theorem predicateFuzzyThereExistsCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (N : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        σ params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ForAll` threshold cut for the
base-type HOL formula "at least two distinct witnesses satisfy `p`".

This specializes the generic counting-cardinality QFM cut at `k = 2` with the
constructed HOL formula and its representation theorem. -/
noncomputable def predicateFuzzyForAllCountingAtLeastTwoBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyForAllCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) params p
    (predicateAtLeastTwoBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable hε0 2 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least two" finite-QFM `ForAll` cut reads out
through the existing HOL interval for its representing formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two" finite-QFM
`ForAll` cut: lower endpoint `1` is exactly provability of the constructed HOL
cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two" finite-QFM
`ForAll` cut: upper endpoint `0` is exactly provability of the negated
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
finite-QFM `ForAll` cut: lower endpoint `0` is exactly non-provability of the
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateFuzzyForAllCountingAtLeastTwoBaseCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
finite-QFM `ForAll` cut: upper endpoint `1` is exactly non-provability of the
negated constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateFuzzyForAllCountingAtLeastTwoBaseCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two" finite-QFM
`ForAll` cut: the interval collapses exactly when the theory decides the
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ThereExists` threshold cut for the
base-type HOL formula "at least two distinct witnesses satisfy `p`".

This is the QFM mass test `PCL ≤ 1 - nearZeroFraction`, specialized at
`PCL = 2 / N`; it is not ordinary HOL existential quantification. -/
noncomputable def predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) params p
    (predicateAtLeastTwoBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable hε0 2 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least two" finite-QFM `ThereExists` cut reads
out through the existing HOL interval for its representing formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two" finite-QFM
`ThereExists` cut: lower endpoint `1` is exactly provability of the constructed
HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two" finite-QFM
`ThereExists` cut: upper endpoint `0` is exactly provability of the negated
constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
finite-QFM `ThereExists` cut: lower endpoint `0` is exactly non-provability of
the constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateFuzzyThereExistsCountingAtLeastTwoBaseCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
finite-QFM `ThereExists` cut: upper endpoint `1` is exactly non-provability of
the negated constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateFuzzyThereExistsCountingAtLeastTwoBaseCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two" finite-QFM
`ThereExists` cut: the interval collapses exactly when the theory decides the
constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (2 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ForAll` threshold cut for the
base-type HOL formula "at least three distinct witnesses satisfy `p`".

This specializes the generic counting-cardinality QFM cut at `k = 3` with the
constructed HOL formula and its representation theorem. -/
noncomputable def predicateFuzzyForAllCountingAtLeastThreeBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyForAllCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) params p
    (predicateAtLeastThreeBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastThreeBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable hε0 3 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least three" finite-QFM `ForAll` cut reads out
through the existing HOL interval for its representing formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three" finite-QFM
`ForAll` cut: lower endpoint `1` is exactly provability of the constructed HOL
cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three" finite-QFM
`ForAll` cut: upper endpoint `0` is exactly provability of the negated
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
finite-QFM `ForAll` cut: lower endpoint `0` is exactly non-provability of the
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateFuzzyForAllCountingAtLeastThreeBaseCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
finite-QFM `ForAll` cut: upper endpoint `1` is exactly non-provability of the
negated constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateFuzzyForAllCountingAtLeastThreeBaseCut,
    predicateFuzzyForAllCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three" finite-QFM
`ForAll` cut: the interval collapses exactly when the theory decides the
constructed HOL cardinality formula. -/
theorem predicateFuzzyForAllCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator finite-QFM `ThereExists` threshold cut for the
base-type HOL formula "at least three distinct witnesses satisfy `p`".

This is the QFM mass test `PCL ≤ 1 - nearZeroFraction`, specialized at
`PCL = 3 / N`; it is not ordinary HOL existential quantification. -/
noncomputable def predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) params p
    (predicateAtLeastThreeBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastThreeBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable hε0 3 N hNpos hPCL hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least three" finite-QFM `ThereExists` cut reads
out through the existing HOL interval for its representing formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three" finite-QFM
`ThereExists` cut: lower endpoint `1` is exactly provability of the constructed
HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three" finite-QFM
`ThereExists` cut: upper endpoint `0` is exactly provability of the negated
constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
finite-QFM `ThereExists` cut: lower endpoint `0` is exactly non-provability of
the constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateFuzzyThereExistsCountingAtLeastThreeBaseCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
finite-QFM `ThereExists` cut: upper endpoint `1` is exactly non-provability of
the negated constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateFuzzyThereExistsCountingAtLeastThreeBaseCut,
    predicateFuzzyThereExistsCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three" finite-QFM
`ThereExists` cut: the interval collapses exactly when the theory decides the
constructed HOL cardinality formula. -/
theorem predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hε0 : params.ε = 0)
    (N : Nat) (hNpos : 0 < N)
    (hPCL : params.PCL = (3 : ℝ) / (N : ℝ))
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b params p hp0 hObj hMeasurable hε0 N hNpos hPCL hCardEq)
      enum henum hCons hT0 hEM

/-- On a finite carrier whose cardinality is exactly `N`, normalized counting
capacity is strictly positive exactly when the subset has at least one
element. -/
theorem FuzzyCapacity.countingCapacity_pos_iff_one_le_ncard_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    0 <
        ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ↔
      1 ≤ A.ncard := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  change 0 < ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) ↔
      1 ≤ A.ncard
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hPos
    have hNumPos : 0 < (A.ncard : ℝ) :=
      (div_pos_iff_of_pos_right hNposR).mp hPos
    have hNatPos : 0 < A.ncard := by
      exact_mod_cast hNumPos
    exact Nat.succ_le_of_lt hNatPos
  · intro hOne
    have hNumPos : 0 < (A.ncard : ℝ) := by
      exact_mod_cast hOne
    exact (div_pos_iff_of_pos_right hNposR).mpr hNumPos

/-- On a finite carrier whose cardinality is exactly `N`, normalized counting
capacity is below `1` exactly when the subset misses at least one element. -/
theorem FuzzyCapacity.countingCapacity_lt_one_iff_ncard_add_one_le_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) < 1 ↔
      A.ncard + 1 ≤ N := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  change ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) < 1 ↔
      A.ncard + 1 ≤ N
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hLt
    have hCast : (A.ncard : ℝ) < (N : ℝ) :=
      (div_lt_one hNposR).mp hLt
    have hNat : A.ncard < N := by
      exact_mod_cast hCast
    exact (Nat.lt_iff_add_one_le.mp hNat)
  · intro hAdd
    have hNat : A.ncard < N :=
      Nat.lt_iff_add_one_le.mpr hAdd
    have hCast : (A.ncard : ℝ) < (N : ℝ) := by
      exact_mod_cast hNat
    exact (div_lt_one hNposR).mpr hCast

/-- On an exact finite carrier, the strict open interval `0 < countingCapacity
A < 1` is exactly the proper-cardinality condition: at least one member and at
least one missing member. -/
theorem FuzzyCapacity.countingCapacity_pos_and_lt_one_iff_proper_cardinality_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    0 <
          ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ∧
        ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) < 1 ↔
      1 ≤ A.ncard ∧ A.ncard + 1 ≤ N := by
  rw [FuzzyCapacity.countingCapacity_pos_iff_one_le_ncard_of_card_eq
      (U := U) A N hNpos hCard,
    FuzzyCapacity.countingCapacity_lt_one_iff_ncard_add_one_le_of_card_eq
      (U := U) A N hNpos hCard]

/-- A nonempty predicate extension has normalized counting capacity at least
`1 / N` when the finite carrier has cardinality at most `N`.

This is the small but load-bearing arithmetic fact behind the first genuinely
fractional QFM/counting cut below.  The uniform carrier bound is essential: a
fixed positive threshold cannot represent nonempty existence over arbitrarily
large finite domains. -/
theorem predicateCountingCapacityExtension_ge_one_div_of_models_exists_of_card_le
    (M : HenkinModel.{u, v, w} Base Const)
    (tau : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M tau)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M tau)]
    (p : UnaryPredicate (Base := Base) (Const := Const) tau)
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      Fintype.card (PredicateObject (Base := Base) (Const := Const) M tau) ≤ N)
    (hModels :
      HenkinModel.models M
        (predicateExistsFormula (Base := Base) (Const := Const) tau p)) :
    (1 : ℝ) / (N : ℝ) ≤
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject (Base := Base) (Const := Const) M tau))
        (predicateExtension (Base := Base) (Const := Const) M tau p) :
          unitInterval) : ℝ) := by
    classical
    have hExtNonempty :
        (predicateExtension (Base := Base) (Const := Const) M tau p).Nonempty := by
      rcases
          (models_predicateExistsFormula_iff
            (Base := Base) (Const := Const) M tau p).1 hModels with
        ⟨x, hx⟩
      exact ⟨x, hx⟩
    exact
      (FuzzyCapacity.countingCapacity_ge_one_div_of_nonempty_of_card_le
        (U := (PredicateObject (Base := Base) (Const := Const) M tau))
        (predicateExtension (Base := Base) (Const := Const) M tau p)
        N hNpos hCard hExtNonempty)

/-- Guarded fractional counting-capacity cut for HOL existence.

For a fixed positive threshold `θ`, normalized counting capacity of a predicate
extension represents ordinary HOL `Exists` once every canonical carrier is
uniformly bounded by `N` and `θ ≤ 1/N`.  This is the first fractional
QFM/counting definable cut: unlike Boolean acceptance scores, the theorem needs
an explicit finite-carrier lower-bound hypothesis. -/
noncomputable def predicateCountingCapacityExistsPositiveThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := theta
    formula := predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact le_trans htheta_le
          (predicateCountingCapacityExtension_ge_one_div_of_models_exists_of_card_le
            (Base := Base) (Const := WithParams Const) M.1 tau p
            N hNpos (hCard M) hModels)
      · intro hGe
        by_contra hNotModels
        have hExtEmpty :
            predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p = ∅ := by
          ext x
          constructor
          · intro hx
            have hPred :
                predicateHoldsAt
                  (Base := Base) (Const := WithParams Const) M.1 tau p x := by
              simpa [predicateExtension] using hx
            exact False.elim
              (hNotModels
                ((models_predicateExistsFormula_iff
                  (Base := Base) (Const := WithParams Const) M.1 tau p).2
                  ⟨x, hPred⟩))
          · intro hx
            simp at hx
        have hScore0 :
            ((FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 0 := by
          have hCap :
              FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) =
                (0 : unitInterval) := by
            simp [FuzzyCapacity.countingCapacity, hExtEmpty,
              FuzzyCapacity.countingValue_empty
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))]
          exact congrArg Subtype.val hCap
        have hNotGe : ¬ theta ≤
            ((FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) := by
          simpa [hScore0] using (not_le.mpr htheta_pos)
        exact hNotGe hGe }

/-- The guarded fractional counting-capacity cut has exactly the formula-level
credal interval of its representing HOL existence formula.

This is the readout that keeps the fractional cut tied to the sealed
formula-level completeness machinery: the numeric score is new, but the
interval is still the existing extensional HOL interval for the certified
threshold formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM =
      extensionalTheoryCredalHOLFormulaIntervalOfConsistent
        (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the guarded fractional counting-existence cut:
lower endpoint `1` is exactly provability of the representing HOL existence
formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the guarded fractional counting-existence cut:
upper endpoint `0` is exactly provability of the negation of the representing
HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the guarded fractional
counting-existence cut: lower endpoint `0` is exactly non-provability of the
representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the guarded fractional
counting-existence cut: upper endpoint `1` is exactly non-provability of the
negation of the representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the guarded fractional counting-existence cut:
the certified fractional-counting interval collapses exactly when the theory
decides the representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete HOL formula
`∃ x, p x`.

Under an exact carrier-size guard `N`, the formula represents
`1 / N ≤ countingCapacity(ext p)`: at least one admissible object lies in the
predicate extension. Unlike the base-type `at least two` and `at least three`
formulae, this construction works at every HOL type because it does not compare
objects by equality. -/
noncomputable def predicateCountingCapacityExistsExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := ((1 : Nat) : ℝ) / (N : ℝ)
    formula := predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i)
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            1 N hNpos (hCardEq M)).2
            ((models_predicateExistsFormula_iff_one_le_ncard_extension
              (Base := Base) (Const := WithParams Const) M.1 tau p).1 hModels)
      · intro hGe
        exact
          (models_predicateExistsFormula_iff_one_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 tau p).2
            ((FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p)
              1 N hNpos (hCardEq M)).1 hGe) }

/-- The concrete exact-denominator existential counting cut reads out through
the existing HOL interval for `∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the concrete exact-denominator existential counting
cut: lower endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete exact-denominator existential counting
cut: upper endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete exact-denominator
existential counting cut: lower endpoint `0` is exactly non-provability of
`∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete exact-denominator
existential counting cut: upper endpoint `1` is exactly non-provability of
`¬ ∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete exact-denominator existential
counting cut: the interval collapses exactly when the theory decides
`∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact rational counting-capacity cut from a cardinality-threshold
calibration formula.

If a param-free closed HOL formula `χ` represents "the predicate extension has
at least `k` elements" in every extensional theory model, and the carrier for
the predicate type has exactly `N` objects in every such model, then `χ`
represents the normalized counting-capacity threshold `k / N`.

This is deliberately a calibrated cut: this file does not invent a syntax for
"there are at least `k` distinct witnesses".  The caller must supply the
formula and the proof that it represents the cardinality event. -/
noncomputable def predicateCountingCapacityCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := (k : ℝ) / (N : ℝ)
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 ((hχRep M).1 hModels)
      · intro hGe
        exact (hχRep M).2
          ((FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hGe) }

/-- The calibrated cardinality-threshold counting cut reads out through the
existing HOL interval for its supplied representing formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for exact-denominator lower-cardinality counting cuts:
lower endpoint `1` is exactly provability of the supplied cardinality formula.
-/
theorem predicateCountingCapacityCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator lower-cardinality counting cuts:
upper endpoint `0` is exactly provability of the negation of the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator lower-cardinality
counting cuts: lower endpoint `0` is exactly non-provability of the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator lower-cardinality
counting cuts: upper endpoint `1` is exactly non-provability of the negation of
the supplied cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator lower-cardinality counting cuts:
the certified interval collapses exactly when the theory decides the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete base-type HOL
formula "at least two distinct witnesses satisfy `p`".

This is the first nontrivial cardinality-threshold cut whose representing
formula is constructed here rather than supplied by the caller.  It is
restricted to base HOL types because equality at higher types is extensional
equivalence, while the normalized counting score counts admissible objects. -/
noncomputable def predicateCountingCapacityAtLeastTwoBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastTwoBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 2 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least two" counting cut reads out through the
existing HOL interval for its representing formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two" counting cut:
lower endpoint `1` is exactly provability of the constructed HOL cardinality
formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two" counting cut:
upper endpoint `0` is exactly provability of the negation of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
counting cut: lower endpoint `0` is exactly non-provability of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
counting cut: upper endpoint `1` is exactly non-provability of the negation of
the constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two" counting
cut: the interval collapses exactly when the theory decides the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete base-type HOL
formula "at least three distinct witnesses satisfy `p`".

This specializes the lower-cardinality threshold package at `k = 3` with a
constructed HOL formula and a theorem proving that the formula represents
`3 ≤ ncard(ext p)` in every canonical completion. -/
noncomputable def predicateCountingCapacityAtLeastThreeBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastThreeBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastThreeBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 3 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least three" counting cut reads out through the
existing HOL interval for its representing formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three" counting
cut: lower endpoint `1` is exactly provability of the constructed HOL
cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three" counting
cut: upper endpoint `0` is exactly provability of the negation of the
constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
counting cut: lower endpoint `0` is exactly non-provability of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
counting cut: upper endpoint `1` is exactly non-provability of the negation of
the constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three" counting
cut: the interval collapses exactly when the theory decides the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact rational complement-counting cut from an upper-cardinality calibration
formula.

If a param-free closed HOL formula `χ` represents
`ncard (ext p) + k ≤ N` in every extensional theory model, and the carrier for
the predicate type has exactly `N` objects in every such model, then `χ`
represents the complementary normalized counting-capacity threshold
`k / N ≤ 1 - countingCapacity(ext p)`.

This is the dual of `predicateCountingCapacityCardinalityThresholdCut`: it
certifies upper/absence-side rational events without pretending that Boolean
negation of a lower-cardinality formula is the same thing as a numeric
complement threshold. -/
noncomputable def predicateCountingCapacityComplementCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      1 - ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := (k : ℝ) / (N : ℝ)
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 ((hχRep M).1 hModels)
      · intro hGe
        exact (hχRep M).2
          ((FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hGe) }

/-- The calibrated complement-cardinality threshold cut reads out through the
existing HOL interval for its supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for exact-denominator complement-cardinality counting
cuts: lower endpoint `1` is exactly provability of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator complement-cardinality counting
cuts: upper endpoint `0` is exactly provability of the negation of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator complement-cardinality
counting cuts: lower endpoint `0` is exactly non-provability of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator complement-cardinality
counting cuts: upper endpoint `1` is exactly non-provability of the negation of
the supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator complement-cardinality counting
cuts: the certified interval collapses exactly when the theory decides the
supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Exact-denominator complement counting-capacity cut for the concrete HOL
formula `∃ x, ¬ p x`.

Under an exact carrier-size guard `N`, the formula represents
`1 / N ≤ 1 - countingCapacity(ext p)`: there is at least one admissible object
outside the predicate extension.  Unlike the base-type `at least two`
cardinality formula, this construction works at every HOL type because it does
not compare two objects by equality. -/
noncomputable def predicateCountingCapacityExistsNotComplementCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityComplementCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsNotFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 tau p N (hCardEq M))

/-- The concrete non-witness complement cut reads out through the existing HOL
interval for `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the concrete non-witness complement cut: lower
endpoint `1` is exactly provability of `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete non-witness complement cut: upper
endpoint `0` is exactly provability of `¬ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete non-witness complement
cut: lower endpoint `0` is exactly non-provability of `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete non-witness complement
cut: upper endpoint `1` is exactly non-provability of `¬ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete non-witness complement cut: the
interval collapses exactly when the theory decides `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact-denominator finite-frequency band cut for normalized counting
capacity.

The lower formula `χLower` represents `kLower ≤ ncard(ext p)`.  The upper-side
formula `χUpper` represents `ncard(ext p) + kMissing ≤ N`, i.e. enough
complement mass remains.  Their conjunction therefore represents the rational
band
`kLower / N ≤ countingCapacity(ext p)` and
`kMissing / N ≤ 1 - countingCapacity(ext p)`.

The result is deliberately built by composing the two existing calibrated cuts
through `andCut`: this is a consumer package over certified threshold events,
not a new interval semantics. -/
noncomputable def predicateCountingCapacityCardinalityBandCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p χLower hχLower0 hObj hMeasurable kLower N hNpos hCardEq
    hχLowerRep).andCut
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χUpper hχUpper0 hObj hMeasurable kMissing N hNpos hCardEq
        hχUpperRep)

/-- The exact-denominator band cut is true in a canonical model exactly when
both finite-cardinality side conditions hold there. -/
theorem predicateCountingCapacityCardinalityBandCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityCardinalityBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
      kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep).threshold ≤
        (predicateCountingCapacityCardinalityBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
          kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep).score M ↔
      kLower ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          kMissing ≤ N := by
  classical
  let CLower :=
    predicateCountingCapacityCardinalityThresholdCut
      (Base := Base) (Const := Const) (T := T)
      tau p χLower hχLower0 hObj hMeasurable kLower N hNpos hCardEq
      hχLowerRep
  let CUpper :=
    predicateCountingCapacityComplementCardinalityThresholdCut
      (Base := Base) (Const := Const) (T := T)
      tau p χUpper hχUpper0 hObj hMeasurable kMissing N hNpos hCardEq
      hχUpperRep
  change (CLower.andCut (Base := Base) (Const := Const) CUpper).threshold ≤
        (CLower.andCut (Base := Base) (Const := Const) CUpper).score M ↔
      kLower ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          kMissing ≤ N
  rw [ExtensionalDefinableCut.andCut_ge_iff]
  constructor
  · intro hBoth
    exact
      ⟨(hχLowerRep M).1 ((CLower.represents_ge M).2 hBoth.1),
        (hχUpperRep M).1 ((CUpper.represents_ge M).2 hBoth.2)⟩
  · intro hBoth
    exact
      ⟨(CLower.represents_ge M).1 ((hχLowerRep M).2 hBoth.1),
        (CUpper.represents_ge M).1 ((hχUpperRep M).2 hBoth.2)⟩

/-- The calibrated finite-frequency band cut reads out through the existing
HOL interval for the conjunction of its supplied lower and upper formulas. -/
theorem predicateCountingCapacityCardinalityBandCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and χLower χUpper) := rfl

/-- Endpoint tightness for exact-denominator finite-frequency bands: lower
endpoint `1` is exactly provability of the supplied lower/upper cardinality
conjunction.

This theorem is deliberately a thin specialization of
`ExtensionalDefinableCut.lower_eq_one_iff_provable`; the mathematical content
is the already-certified `represents_ge` field of
`predicateCountingCapacityCardinalityBandCut`. -/
theorem predicateCountingCapacityCardinalityBandCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and χLower χUpper) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator finite-frequency bands: upper
endpoint `0` is exactly provability of the negation of the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator finite-frequency
bands: lower endpoint `0` is exactly non-provability of the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and χLower χUpper) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator finite-frequency
bands: upper endpoint `1` is exactly non-provability of the negation of the
supplied lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator finite-frequency bands: the
certified band interval collapses exactly when the theory decides the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
          (.and χLower χUpper) ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T
          (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-! ### Concrete constructed finite-frequency bands -/

/-- Concrete all-HOL finite-frequency band cut for normalized counting
capacity.

Under an exact carrier-size guard `N`, this cut certifies the proper
nontrivial band `1 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)`: there is at least one witness for `p`,
and at least one admissible object does not satisfy `p`.  Unlike the
base-type two/three-witness cuts, this construction works at every HOL type
because neither side compares two objects by equality. -/
noncomputable def predicateCountingCapacityExistsAndExistsNotBandCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityCardinalityBandCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p)
    (predicateExistsNotFormula
      (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 tau p)
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 tau p N
          (hCardEq M))

/-- The concrete all-HOL proper finite-frequency band event holds exactly when
there is at least one predicate witness and at least one non-witness. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityExistsAndExistsNotBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityExistsAndExistsNotBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      1 ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          1 ≤ N := by
  exact
    predicateCountingCapacityCardinalityBandCut_ge_iff
      (Base := Base) (Const := Const) (T := T)
      tau p
      (predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p)
      (predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p)
      (fun ρ i =>
        noConstOccurrence_predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
      (fun ρ i =>
        noConstOccurrence_predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
      hObj hMeasurable 1 1 N hNpos hCardEq
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsFormula_iff_one_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 tau p)
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
            (Base := Base) (Const := WithParams Const) M.1 tau p N
            (hCardEq M))
      M

/-- Numeric readout for the concrete all-HOL proper finite-frequency band:
under the exact carrier-size guard, the certified band event is exactly that
the normalized counting capacity of the predicate extension is strictly between
`0` and `1`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff_countingCapacity_pos_and_lt_one
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityExistsAndExistsNotBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityExistsAndExistsNotBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      0 <
          ((FuzzyCapacity.countingCapacity
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) ∧
        ((FuzzyCapacity.countingCapacity
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) < 1 := by
  letI := hObj M
  letI := hMeasurable M
  rw [predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff
    (Base := Base) (Const := Const) (T := T)
    tau p hp0 hObj hMeasurable N hNpos hCardEq M]
  exact
    (FuzzyCapacity.countingCapacity_pos_and_lt_one_iff_proper_cardinality_of_card_eq
      (U := (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
      (predicateExtension
        (Base := Base) (Const := WithParams Const) M.1 tau p)
      N hNpos (hCardEq M)).symm

/-- The concrete all-HOL proper finite-frequency band reads out through the
existing HOL interval for `∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and
            (predicateExistsFormula
              (Base := Base) (Const := WithParams Const) tau p)
            (predicateExistsNotFormula
              (Base := Base) (Const := WithParams Const) tau p)) := rfl

/-- Endpoint tightness for the concrete all-HOL proper finite-frequency band:
lower endpoint `1` is exactly provability of `∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete all-HOL proper finite-frequency band:
upper endpoint `0` is exactly provability of the negation of
`∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete all-HOL proper
finite-frequency band: lower endpoint `0` is exactly non-provability of the
conjunction of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete all-HOL proper
finite-frequency band: upper endpoint `1` is exactly non-provability of the
negation of the conjunction of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete all-HOL proper finite-frequency
band: the interval collapses exactly when the theory decides the conjunction
of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete base-type finite-frequency band cut for normalized counting
capacity.

Under an exact carrier-size guard `N`, this cut certifies the band
`2 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)`: at least two witnesses satisfy `p`, and
at least one admissible base object does not.  The lower side uses the
constructed base-type HOL formula with equality; the complement side uses the
constructed non-witness formula. -/
noncomputable def predicateCountingCapacityTwoToAllButOneBaseBandCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityCardinalityBandCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastTwoBaseFormula
      (Base := Base) (Const := WithParams Const) b p)
    (predicateExistsNotFormula
      (Base := Base) (Const := WithParams Const) (.base b) p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) (.base b) p (hp0 ρ i))
    hObj hMeasurable 2 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 (.base b) p N
          (hCardEq M))

/-- The concrete base finite-frequency band event holds exactly when there are
at least two predicate witnesses and at least one non-witness. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityTwoToAllButOneBaseBandCut
      (Base := Base) (Const := Const) (T := T)
      b p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityTwoToAllButOneBaseBandCut
          (Base := Base) (Const := Const) (T := T)
          b p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      2 ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p).ncard +
          1 ≤ N := by
  exact
    predicateCountingCapacityCardinalityBandCut_ge_iff
      (Base := Base) (Const := Const) (T := T)
      (.base b) p
      (predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p)
      (predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) (.base b) p)
      (fun ρ i =>
        noConstOccurrence_predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
      (fun ρ i =>
        noConstOccurrence_predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) (.base b) p (hp0 ρ i))
      hObj hMeasurable 2 1 N hNpos hCardEq
      (fun M => by
        letI := hObj M
        exact
          models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 b p)
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p N
            (hCardEq M))
      M

/-- The concrete base finite-frequency band reads out through the existing HOL
interval for the conjunction of its two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and
            (predicateAtLeastTwoBaseFormula
              (Base := Base) (Const := WithParams Const) b p)
            (predicateExistsNotFormula
              (Base := Base) (Const := WithParams Const) (.base b) p)) := rfl

/-- Endpoint tightness for the concrete base finite-frequency band: lower
endpoint `1` is exactly provability of the conjunction of its two constructed
cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base finite-frequency band: upper
endpoint `0` is exactly provability of the negation of the conjunction of its
two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base finite-frequency
band: lower endpoint `0` is exactly non-provability of the conjunction of its
two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base finite-frequency
band: upper endpoint `1` is exactly non-provability of the negation of the
conjunction of its two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base finite-frequency band: the
interval collapses exactly when the theory decides the conjunction of its two
constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

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

/-- The calibrated Sugeno endpoint cut reads out through the existing HOL
formula interval for the representing universal-predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for calibrated Sugeno endpoint cuts: lower endpoint `1`
is exactly provability of the HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for calibrated Sugeno endpoint cuts: upper endpoint `0`
is exactly provability of the negated HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for calibrated Sugeno endpoint cuts: the interval
collapses exactly when the theory decides the HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

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

/-- The counting-capacity Sugeno endpoint cut reads out through the existing
HOL formula interval for the representing universal-predicate formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_intervalOfConsistent
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for counting-capacity Sugeno endpoint cuts: lower
endpoint `1` is exactly provability of the HOL universal predicate formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_lower_eq_one_iff_provable
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for counting-capacity Sugeno endpoint cuts: upper
endpoint `0` is exactly provability of the negated HOL universal predicate
formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for counting-capacity Sugeno endpoint cuts: the
interval collapses exactly when the theory decides the HOL universal predicate
formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_width_eq_zero_iff_decides
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
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Exact-denominator normalized-counting Sugeno cut for HOL-induced crisp
profiles.

For crisp HOL predicates, Sugeno aggregation against normalized counting
capacity is exactly the counting capacity of the predicate extension.  Thus
the same exact-denominator cardinality certificate used for counting capacity
also certifies the fractional Sugeno event `k / N ≤ Sugeno(counting, p)`.
This is still a counting-capacity result; arbitrary capacities require their
own threshold representation theorem. -/
noncomputable def predicateSugenoCountingCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((sugenoScoreInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject
            (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := (k : ℝ) / (N : ℝ)
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      have hScoreEq :
          ((sugenoScoreInf
            (FuzzyCapacity.countingCapacity
              (U := PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) =
          (((FuzzyCapacity.countingCapacity
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) := by
        rw [predicateSugenoScoreInf_eq_capacity_extension
          (Base := Base) (Const := WithParams Const) M.1 tau
          (FuzzyCapacity.countingCapacity
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)) p]
      constructor
      · intro hModels
        have hCount : k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard :=
          (hχRep M).1 hModels
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) :
                unitInterval) : ℝ) :=
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 hCount
        simpa [hScoreEq] using hCap
      · intro hGe
        apply (hχRep M).2
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) :
                unitInterval) : ℝ) := by
          simpa [hScoreEq] using hGe
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hCap }

/-- The exact-denominator normalized-counting Sugeno cut reads out through the
existing HOL interval for the supplied cardinality-threshold formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: lower endpoint `1` is exactly provability of
the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: upper endpoint `0` is exactly provability of
the negated supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the generic exact-denominator
normalized-counting Sugeno cardinality-threshold cut: lower endpoint `0` is
exactly non-provability of the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the generic exact-denominator
normalized-counting Sugeno cardinality-threshold cut: upper endpoint `1` is
exactly non-provability of the negated supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: the interval collapses exactly when the
theory decides the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the HOL
existence formula `∃ x, p x`.

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the ordinary HOL existence formula at
threshold `1 / N`. This works at every HOL type because it does not rely on
object equality. -/
noncomputable def predicateSugenoCountingExistsExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 tau p)

/-- The concrete HOL-existence normalized-counting Sugeno cut reads out
through the existing HOL interval for `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the HOL-existence normalized-counting Sugeno cut:
lower endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-existence normalized-counting Sugeno cut:
upper endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-existence normalized-counting
Sugeno cut: lower endpoint `0` is exactly non-provability of `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  simpa [predicateSugenoCountingExistsExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-existence normalized-counting
Sugeno cut: upper endpoint `1` is exactly non-provability of `¬ ∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  simpa [predicateSugenoCountingExistsExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-existence normalized-counting Sugeno cut:
the interval collapses exactly when the theory decides `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the HOL
universal formula `∀ x, p x`.

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity.
At the exact denominator threshold `N / N`, the numeric event is represented by
ordinary HOL universal truth under the explicit exact-carrier guards. -/
noncomputable def predicateSugenoCountingUniversalExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable N N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateForAllFormula_iff_card_le_ncard_extension_of_card_eq
          (Base := Base) (Const := WithParams Const) M.1 tau p N (hCardEq M))

/-- The concrete HOL-universal normalized-counting Sugeno cut reads out
through the existing HOL interval for `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the HOL-universal normalized-counting Sugeno cut:
lower endpoint `1` is exactly provability of `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-universal normalized-counting Sugeno cut:
upper endpoint `0` is exactly provability of `¬ ∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-universal normalized-counting
Sugeno cut: lower endpoint `0` is exactly non-provability of `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  simpa [predicateSugenoCountingUniversalExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-universal normalized-counting
Sugeno cut: upper endpoint `1` is exactly non-provability of `¬ ∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  simpa [predicateSugenoCountingUniversalExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-universal normalized-counting Sugeno cut:
the interval collapses exactly when the theory decides `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the
base-type HOL formula "at least two distinct witnesses satisfy `p`".

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the constructed base-type cardinality
formula at threshold `2 / N`. -/
noncomputable def predicateSugenoCountingAtLeastTwoBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastTwoBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 2 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least two" normalized-counting Sugeno cut
reads out through the existing HOL interval for its representing formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: lower endpoint `1` is exactly provability of
the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: upper endpoint `0` is exactly provability of
the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: lower endpoint `0` is exactly non-provability
of the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateSugenoCountingAtLeastTwoBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: upper endpoint `1` is exactly non-provability
of the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateSugenoCountingAtLeastTwoBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: the interval collapses exactly when the theory
decides the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the
base-type HOL formula "at least three distinct witnesses satisfy `p`".

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the constructed base-type cardinality
formula at threshold `3 / N`. -/
noncomputable def predicateSugenoCountingAtLeastThreeBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastThreeBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastThreeBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 3 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least three" normalized-counting Sugeno cut
reads out through the existing HOL interval for its representing formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: lower endpoint `1` is exactly provability of
the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: upper endpoint `0` is exactly provability of
the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: lower endpoint `0` is exactly non-provability
of the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateSugenoCountingAtLeastThreeBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: upper endpoint `1` is exactly non-provability
of the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateSugenoCountingAtLeastThreeBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: the interval collapses exactly when the theory
decides the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

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

/-- Joint-cut version of saturated source-side analogy transfer.

This is the rule-facing use of `andCut`: the two premises "source-side
similarity is saturated" and "`q` fully inherits to `r`" are carried by one
certified conjunctive cut. The proof deliberately reuses the existing
source-side transfer theorem after unpacking the joint endpoint, so no parallel
analogy semantics is introduced. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity_jointCut
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
    (hJointLower :
      (((predicateVocabularySimilarityGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hqE hpI hSim0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q r
          hObj hqE hrI hQR0)).intervalOfConsistent
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
  have hBothAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M ∧ Cqr.threshold ≤ Cqr.score M :=
    (Csim.andCut_lower_eq_one_iff_forall_both_ge
      (Base := Base) (Const := Const) Cqr enum henum hCons hT0 hEM).1 hJointLower
  have hSimLower :
      (Csim.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).1)
  have hQRLower :
      (Cqr.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Cqr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).2)
  exact
    predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q r
      hObj hpE hpI hqE hqI hrI hSim0 hQR0 hPR0
      hSimLower hQRLower

/-- Rule-implication cut for saturated source-side analogy transfer.

Rather than taking the two saturated premises as global hypotheses, this
theorem packages the whole exact-threshold source-side analogy rule as one
certified implication cut:

`(similarity(p,q) = 1 ∧ inheritance(q,r) = 1) -> inheritance(p,r) = 1`.

The proof is pointwise over the canonical extensional theory-model family and
uses the existing full-inheritance source-similarity theorem, so this is a rule
gate over the established extensional/intensional machinery, not a duplicate
analogy semantics. -/
theorem predicateVocabularyFullInheritanceGeOneCut_sourceSimilarityRuleImpCut_lower_eq_one
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
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r))) :
    ((((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hQR0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p r
        hObj hpE hrI hPR0)).intervalOfConsistent
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
  exact
    ((Csim.andCut (Base := Base) (Const := Const) Cqr).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpr enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        letI := hObj M
        have hBoth :
            Csim.threshold ≤ Csim.score M ∧ Cqr.threshold ≤ Cqr.score M :=
          (Csim.andCut_ge_iff (Base := Base) (Const := Const) Cqr M).mp hJoint
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hBoth.1
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
          simpa [Cqr, predicateVocabularyFullInheritanceGeOneCut] using hBoth.2
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

/-- Joint-cut version of saturated target-side analogy transfer.

This is the companion rule-facing use of `andCut`: the two premises "`p` fully
inherits to `q`" and "target-side similarity between `q` and `r` is saturated"
are carried by one certified conjunctive cut. As with the source-side version,
the proof unpacks the joint endpoint and reuses the existing target-side
transfer theorem. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity_jointCut
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
    (hJointLower :
      (((predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hPQ0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularySimilarityGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q r
          hObj hqE hrI hrE hqI hSim0)).intervalOfConsistent
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
  have hBothAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cpq.threshold ≤ Cpq.score M ∧ Csim.threshold ≤ Csim.score M :=
    (Cpq.andCut_lower_eq_one_iff_forall_both_ge
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM).1 hJointLower
  have hPQLower :
      (Cpq.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Cpq.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).1)
  have hSimLower :
      (Csim.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).2)
  exact
    predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q r
      hObj hpE hqE hqI hrE hrI hPQ0 hSim0 hPR0
      hPQLower hSimLower

/-- Rule-implication cut for saturated target-side analogy transfer.

This packages the exact-threshold target-side analogy rule as one certified
implication cut:

`(inheritance(p,q) = 1 ∧ similarity(q,r) = 1) -> inheritance(p,r) = 1`.

As with the source-side rule cut, the proof is pointwise over the canonical
extensional theory-model family and reuses the existing target-side transfer
theorem. -/
theorem predicateVocabularyFullInheritanceGeOneCut_targetSimilarityRuleImpCut_lower_eq_one
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
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r))) :
    ((((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hrE hqI hSim0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p r
        hObj hpE hrI hPR0)).intervalOfConsistent
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
  exact
    ((Cpq.andCut (Base := Base) (Const := Const) Csim).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpr enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        letI := hObj M
        have hBoth :
            Cpq.threshold ≤ Cpq.score M ∧ Csim.threshold ≤ Csim.score M :=
          (Cpq.andCut_ge_iff (Base := Base) (Const := Const) Csim M).mp hJoint
        have hPQGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Cpq, predicateVocabularyFullInheritanceGeOneCut] using hBoth.1
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
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hBoth.2
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

/-! ## Cut-level similarity / inheritance conversion -/

/-- Certified conversion from saturated predicate similarity to the forward
directed full-inheritance cut.

At threshold `1`, predicate similarity is represented by HOL predicate
equivalence, hence it entails the forward predicate-implication formula.  The
result is packaged as an implication cut so downstream PLN rule surfaces can
consume the conversion without duplicating the similarity semantics. -/
theorem predicateVocabularySimilarityGeOneCut_forwardInheritanceRuleImpCut_lower_eq_one
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
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    (((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  exact
    (Csim.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpq enum henum hCons hT0 hEM).2 <|
      fun M hSim => by
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (Csim.represents_ge M).mpr hSim
        have hImp : HenkinModel.models M.1 Cpq.formula :=
          (HenkinModel.models_and M.1).mp hIff |>.1
        exact (Cpq.represents_ge M).mp hImp

/-- Certified conversion from saturated predicate similarity to the reverse
directed full-inheritance cut. -/
theorem predicateVocabularySimilarityGeOneCut_reverseInheritanceRuleImpCut_lower_eq_one
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
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p))) :
    (((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q p
        hObj hqE hpI hQP0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  exact
    (Csim.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cqp enum henum hCons hT0 hEM).2 <|
      fun M hSim => by
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (Csim.represents_ge M).mpr hSim
        have hImp : HenkinModel.models M.1 Cqp.formula :=
          (HenkinModel.models_and M.1).mp hIff |>.2
        exact (Cqp.represents_ge M).mp hImp

/-- Certified conversion from mutual directed full inheritance to saturated
predicate similarity.

The premise is one conjunctive certified cut for the two directed inheritance
threshold events.  The conclusion is the existing finite-vocabulary similarity
cut, whose representing formula is the conjunction of those two predicate
implications. -/
theorem predicateVocabularySimilarityGeOneCut_of_mutualInheritanceRuleImpCut_lower_eq_one
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
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    ((((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q p
        hObj hqE hpI hQP0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  exact
    ((Cpq.andCut (Base := Base) (Const := Const) Cqp).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        have hBoth :
            Cpq.threshold ≤ Cpq.score M ∧ Cqp.threshold ≤ Cqp.score M :=
          (Cpq.andCut_ge_iff (Base := Base) (Const := Const) Cqp M).mp hJoint
        have hPQModels : HenkinModel.models M.1 Cpq.formula :=
          (Cpq.represents_ge M).mpr hBoth.1
        have hQPModels : HenkinModel.models M.1 Cqp.formula :=
          (Cqp.represents_ge M).mpr hBoth.2
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (HenkinModel.models_and M.1).mpr ⟨hPQModels, hQPModels⟩
        exact (Csim.represents_ge M).mp hIff

/-- Consumer form of saturated similarity-to-forward-inheritance conversion.

If the finite-vocabulary similarity cut is certainly saturated, then the
forward directed full-inheritance cut is certainly saturated.  This is the
exact-threshold, cut-level form of PLN's similarity-to-inheritance conversion;
it reuses the existing representing formula for similarity rather than defining
a parallel numeric conversion. -/
theorem predicateVocabularyFullInheritanceGeOneCut_forward_lower_eq_one_of_similarity
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
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  have hRule :
      ((Csim.impCut (Base := Base) (Const := Const) Cpq).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_forwardInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hSim0 hPQ0
  exact
    Csim.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Cpq enum henum hCons hT0 hEM hRule hSimLower

/-- Consumer form of saturated similarity-to-reverse-inheritance conversion. -/
theorem predicateVocabularyFullInheritanceGeOneCut_reverse_lower_eq_one_of_similarity
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
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  have hRule :
      ((Csim.impCut (Base := Base) (Const := Const) Cqp).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_reverseInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hSim0 hQP0
  exact
    Csim.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Cqp enum henum hCons hT0 hEM hRule hSimLower

/-- Consumer form of mutual-inheritance-to-similarity conversion.

If the two directed full-inheritance cuts are jointly certain, then the
finite-vocabulary similarity cut is certainly saturated.  This is the cut-level
`2inh2sim` endpoint theorem: below threshold `1` the soft formula remains a
semantic envelope, but the exact saturated rule is completeness-tight. -/
theorem predicateVocabularySimilarityGeOneCut_lower_eq_one_of_mutualInheritance_jointCut
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
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hJointLower :
      (((predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hPQ0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q p
          hObj hqE hpI hQP0)).intervalOfConsistent
            (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  have hRule :
      (((Cpq.andCut (Base := Base) (Const := Const) Cqp).impCut
        (Base := Base) (Const := Const) Csim).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_of_mutualInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hPQ0 hQP0 hSim0
  exact
    (Cpq.andCut (Base := Base) (Const := Const) Cqp).lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM hRule hJointLower

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

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
