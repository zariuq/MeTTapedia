import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge

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


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
