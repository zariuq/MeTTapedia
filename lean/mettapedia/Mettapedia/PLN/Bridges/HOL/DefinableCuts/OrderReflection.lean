import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Core
import Mettapedia.PLN.WorldModel.WMReadout

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.PLN.WorldModel

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

def cutEventBoolLE (x y : Bool) : Prop :=
  x = true → y = true

noncomputable def cutScoreEventBool
    {T : ClosedTheorySet (WithParams Const)}
    (score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ)
    (threshold : ℝ)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) : Bool :=
  if threshold ≤ score M then true else false

theorem cutScoreEventBool_eq_true_iff
    {T : ClosedTheorySet (WithParams Const)}
    (score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ)
    (threshold : ℝ)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    cutScoreEventBool (Base := Base) (Const := Const) score threshold M = true ↔
      threshold ≤ score M := by
  classical
  unfold cutScoreEventBool
  by_cases h : threshold ≤ score M <;> simp [h]

def cutFormulaFragmentLE
    {T : ClosedTheorySet (WithParams Const)}
    (formula : ClosedFormula (WithParams Const))
    (M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T) : Prop :=
  HenkinModel.models M.1 formula → HenkinModel.models N.1 formula

def cutScoreFragmentLE
    {T : ClosedTheorySet (WithParams Const)}
    (score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ)
    (threshold : ℝ)
    (M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T) : Prop :=
  threshold ≤ score M → threshold ≤ score N

def CutFragmentOrderTight
    {T : ClosedTheorySet (WithParams Const)}
    (score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ)
    (threshold : ℝ)
    (formula : ClosedFormula (WithParams Const)) : Prop :=
  ∀ M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
    cutFormulaFragmentLE (Base := Base) (Const := Const) formula M N ↔
      cutScoreFragmentLE (Base := Base) (Const := Const) score threshold M N

theorem cutEventReadoutReflects_iff_fragmentOrderTight
    {T : ClosedTheorySet (WithParams Const)}
    (score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ)
    (threshold : ℝ)
    (formula : ClosedFormula (WithParams Const))
    (hMono :
      ∀ {M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T},
        cutFormulaFragmentLE (Base := Base) (Const := Const) formula M N →
          cutScoreFragmentLE (Base := Base) (Const := Const) score threshold M N) :
    (∀ {M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T},
        cutEventBoolLE
          (cutScoreEventBool (Base := Base) (Const := Const) score threshold M)
          (cutScoreEventBool (Base := Base) (Const := Const) score threshold N) →
        cutFormulaFragmentLE (Base := Base) (Const := Const) formula M N) ↔
      CutFragmentOrderTight (Base := Base) (Const := Const) score threshold formula := by
  constructor
  · intro hReflect M N
    constructor
    · intro hFormula
      exact hMono hFormula
    · intro hScore hModelsM
      apply hReflect
      intro hMuM
      exact
        (cutScoreEventBool_eq_true_iff
          (Base := Base) (Const := Const) score threshold N).2
          (hScore
            ((cutScoreEventBool_eq_true_iff
              (Base := Base) (Const := Const) score threshold M).1 hMuM))
      exact hModelsM
  · intro hTight M N hEvent
    exact
      (hTight M N).2 <| by
        intro hScoreM
        have hMuM :
            cutScoreEventBool
              (Base := Base) (Const := Const) score threshold M = true :=
          (cutScoreEventBool_eq_true_iff
            (Base := Base) (Const := Const) score threshold M).2 hScoreM
        have hMuN :
            cutScoreEventBool
              (Base := Base) (Const := Const) score threshold N = true :=
          hEvent hMuM
        exact
          (cutScoreEventBool_eq_true_iff
            (Base := Base) (Const := Const) score threshold N).1 hMuN

theorem ExtensionalDefinableCut.fragmentOrderTight
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    CutFragmentOrderTight (Base := Base) (Const := Const)
      C.score C.threshold C.formula := by
  intro M N
  constructor
  · intro hFormula hScoreM
    have hModelsM : HenkinModel.models M.1 C.formula :=
      (C.represents_ge M).2 hScoreM
    exact (C.represents_ge N).1 (hFormula hModelsM)
  · intro hScore hModelsM
    exact
      (C.represents_ge N).2
        (hScore ((C.represents_ge M).1 hModelsM))

noncomputable def ExtensionalDefinableCut.orderReflectingWMReadout
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    OrderReflectingWMReadout
      (ExtensionalTheoryModel (Base := Base) (Const := Const) T)
      Bool
      (cutFormulaFragmentLE (Base := Base) (Const := Const) C.formula)
      cutEventBoolLE where
  mu := cutScoreEventBool (Base := Base) (Const := Const) C.score C.threshold
  monotone := by
    intro M N hSupport hMu
    have hScoreM : C.threshold ≤ C.score M :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) C.score C.threshold M).1 hMu
    have hModelsM : HenkinModel.models M.1 C.formula :=
      (C.represents_ge M).2 hScoreM
    have hModelsN : HenkinModel.models N.1 C.formula :=
      hSupport hModelsM
    have hScoreN : C.threshold ≤ C.score N :=
      (C.represents_ge N).1 hModelsN
    exact
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) C.score C.threshold N).2 hScoreN
  reflects := by
    intro M N hEvidence hModelsM
    have hScoreM : C.threshold ≤ C.score M :=
      (C.represents_ge M).1 hModelsM
    have hMuM :
        cutScoreEventBool
          (Base := Base) (Const := Const) C.score C.threshold M = true :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) C.score C.threshold M).2 hScoreM
    have hMuN :
        cutScoreEventBool
          (Base := Base) (Const := Const) C.score C.threshold N = true :=
      hEvidence hMuM
    have hScoreN : C.threshold ≤ C.score N :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) C.score C.threshold N).1 hMuN
    exact (C.represents_ge N).2 hScoreN

theorem ExtensionalDefinableCut.orderReflectingWMReadout_reflects
    {T : ClosedTheorySet (WithParams Const)}
    (C : ExtensionalDefinableCut (Base := Base) (Const := Const) T) :
    ∀ {M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T},
      cutEventBoolLE
        ((ExtensionalDefinableCut.orderReflectingWMReadout
          (Base := Base) (Const := Const) C).mu M)
        ((ExtensionalDefinableCut.orderReflectingWMReadout
          (Base := Base) (Const := Const) C).mu N) →
      cutFormulaFragmentLE (Base := Base) (Const := Const) C.formula M N :=
  (ExtensionalDefinableCut.orderReflectingWMReadout
    (Base := Base) (Const := Const) C).reflects

def CertifiedCutFamilyIndex
    {T : ClosedTheorySet (WithParams Const)}
    (cuts : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T)) :=
  { C : ExtensionalDefinableCut (Base := Base) (Const := Const) T // C ∈ cuts }

def certifiedCutFamilyFragmentLE
    {T : ClosedTheorySet (WithParams Const)}
    (cuts : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T))
    (M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T) : Prop :=
  ∀ i : CertifiedCutFamilyIndex (Base := Base) (Const := Const) cuts,
    cutFormulaFragmentLE (Base := Base) (Const := Const) i.1.formula M N

noncomputable def certifiedCutFamilySeparatingWMReadouts
    {T : ClosedTheorySet (WithParams Const)}
    (cuts : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T)) :
    SeparatingWMReadouts
      (CertifiedCutFamilyIndex (Base := Base) (Const := Const) cuts)
      (ExtensionalTheoryModel (Base := Base) (Const := Const) T)
      Bool
      (certifiedCutFamilyFragmentLE (Base := Base) (Const := Const) cuts)
      cutEventBoolLE where
  mu i :=
    cutScoreEventBool
      (Base := Base) (Const := Const) i.1.score i.1.threshold
  monotone := by
    intro i M N hSupport hMu
    have hScoreM : i.1.threshold ≤ i.1.score M :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) i.1.score i.1.threshold M).1 hMu
    have hModelsM : HenkinModel.models M.1 i.1.formula :=
      (i.1.represents_ge M).2 hScoreM
    have hModelsN : HenkinModel.models N.1 i.1.formula :=
      hSupport i hModelsM
    have hScoreN : i.1.threshold ≤ i.1.score N :=
      (i.1.represents_ge N).1 hModelsN
    exact
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) i.1.score i.1.threshold N).2 hScoreN
  separates := by
    intro M N hAll i hModelsM
    have hScoreM : i.1.threshold ≤ i.1.score M :=
      (i.1.represents_ge M).1 hModelsM
    have hMuM :
        cutScoreEventBool
          (Base := Base) (Const := Const) i.1.score i.1.threshold M = true :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) i.1.score i.1.threshold M).2 hScoreM
    have hMuN :
        cutScoreEventBool
          (Base := Base) (Const := Const) i.1.score i.1.threshold N = true :=
      hAll i hMuM
    have hScoreN : i.1.threshold ≤ i.1.score N :=
      (cutScoreEventBool_eq_true_iff
        (Base := Base) (Const := Const) i.1.score i.1.threshold N).1 hMuN
    exact (i.1.represents_ge N).2 hScoreN

theorem certifiedCutFamilySeparatingWMReadouts_separates
    {T : ClosedTheorySet (WithParams Const)}
    (cuts : List (ExtensionalDefinableCut (Base := Base) (Const := Const) T)) :
    ∀ {M N : ExtensionalTheoryModel (Base := Base) (Const := Const) T},
      (∀ i : CertifiedCutFamilyIndex (Base := Base) (Const := Const) cuts,
        cutEventBoolLE
          ((certifiedCutFamilySeparatingWMReadouts
            (Base := Base) (Const := Const) cuts).mu i M)
          ((certifiedCutFamilySeparatingWMReadouts
            (Base := Base) (Const := Const) cuts).mu i N)) →
      certifiedCutFamilyFragmentLE (Base := Base) (Const := Const) cuts M N :=
  (certifiedCutFamilySeparatingWMReadouts
    (Base := Base) (Const := Const) cuts).separates

theorem formulaIndicatorPositiveThresholdCut_fragmentOrderTight
    {T : ClosedTheorySet (WithParams Const)}
    (formula : ClosedFormula (WithParams Const))
    (hFormula0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k) formula)
    (threshold : ℝ)
    (hThresholdPos : 0 < threshold)
    (hThresholdLe : threshold ≤ 1) :
    CutFragmentOrderTight (Base := Base) (Const := Const)
      (formulaIndicatorPositiveThresholdCut
        (Base := Base) (Const := Const) (T := T)
        formula hFormula0 threshold hThresholdPos hThresholdLe).score
      (formulaIndicatorPositiveThresholdCut
        (Base := Base) (Const := Const) (T := T)
        formula hFormula0 threshold hThresholdPos hThresholdLe).threshold
      (formulaIndicatorPositiveThresholdCut
        (Base := Base) (Const := Const) (T := T)
        formula hFormula0 threshold hThresholdPos hThresholdLe).formula :=
  ExtensionalDefinableCut.fragmentOrderTight
    (Base := Base) (Const := Const) (T := T)
    (formulaIndicatorPositiveThresholdCut
      (Base := Base) (Const := Const) (T := T)
      formula hFormula0 threshold hThresholdPos hThresholdLe)

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
