import Foet.EvaluateTheory
import Foet.Paradigms
import Foet.UtilitarianToValue
import Foet.VirtueToValue

set_option autoImplicit false

namespace Foet

universe u

/-! ## Paradigm-specific evaluators (direct) -/

def evaluateDeonticTheoryUnder {World : Type u} (semD : DeonticSemantics World)
    (T : DeontologicalImperativeTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    ValueJudgmentTheory World :=
  fun s =>
    ∃ φ, φ ∈ cp ∧
      ( (s = morallyGood φ ∧ EntailsUnder (deonticSemantics World semD) T ctx { tag := .Obligation, formula := φ }) ∨
        (s = morallyBad φ ∧
          ¬ EntailsUnder (deonticSemantics World semD) T ctx { tag := .Obligation, formula := φ } ∧
          EntailsUnder (deonticSemantics World semD) T ctx { tag := .Prohibition, formula := φ }) ∨
        (s = morallyPermissible φ ∧
          ¬ EntailsUnder (deonticSemantics World semD) T ctx { tag := .Obligation, formula := φ } ∧
          ¬ EntailsUnder (deonticSemantics World semD) T ctx { tag := .Prohibition, formula := φ }) )

def evaluateUtilitarianTheoryUnder {World : Type u} (semU : UtilityAssignmentSemantics World)
    (T : UtilityAssignmentTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    ValueJudgmentTheory World :=
  fun s =>
    ∃ φ, φ ∈ cp ∧
      ( (s = morallyGood φ ∧
          EntailsUnder (utilityAssignmentSemantics World semU) T ctx { tag := 1, formula := φ }) ∨
        (s = morallyBad φ ∧
          ¬ EntailsUnder (utilityAssignmentSemantics World semU) T ctx { tag := 1, formula := φ } ∧
          EntailsUnder (utilityAssignmentSemantics World semU) T ctx { tag := -1, formula := φ }) ∨
        (s = morallyPermissible φ ∧
          ¬ EntailsUnder (utilityAssignmentSemantics World semU) T ctx { tag := 1, formula := φ } ∧
          ¬ EntailsUnder (utilityAssignmentSemantics World semU) T ctx { tag := -1, formula := φ }) )

def evaluateVirtueTargetTheoryUnder {World : Type u} (semT : VirtueTargetSemantics World)
    (T : VirtueTargetTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    ValueJudgmentTheory World :=
  fun s =>
    ∃ φ, φ ∈ cp ∧
      ( (s = morallyGood φ ∧ EntailsUnder (virtueTargetSemantics World semT) T ctx { aspect := .Virtuous, formula := φ }) ∨
        (s = morallyBad φ ∧
          ¬ EntailsUnder (virtueTargetSemantics World semT) T ctx { aspect := .Virtuous, formula := φ } ∧
          EntailsUnder (virtueTargetSemantics World semT) T ctx { aspect := .Vicious, formula := φ }) ∨
        (s = morallyPermissible φ ∧
          ¬ EntailsUnder (virtueTargetSemantics World semT) T ctx { aspect := .Virtuous, formula := φ } ∧
          ¬ EntailsUnder (virtueTargetSemantics World semT) T ctx { aspect := .Vicious, formula := φ }) )

/-! ## Commutation theorems: direct evaluation = evaluation after translation -/

theorem evaluateDeonticTheoryUnder_eq_evaluateTheoryUnder_toValue {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (T : DeontologicalImperativeTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    evaluateDeonticTheoryUnder (World := World) semD T ctx cp =
      evaluateTheoryUnder (World := World) semV (T.toValueJudgmentTheory) ctx cp := by
  funext s
  apply propext
  constructor <;> intro hs
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hObl :
        EntailsUnder (deonticSemantics World semD) T ctx { tag := .Obligation, formula := φ } ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [DeontologicalImperativeTheory.toValueJudgmentTheory, morallyGood, valueSentence, DeonticSentence.toValue,
        deonticToMoralValue] using
        (entails_map_iff_under
          (sem₁ := deonticSemantics World semD)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := DeonticSentence.toValue)
          (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ tag := .Obligation, formula := φ } : DeonticSentence World)))
    have hProh :
        EntailsUnder (deonticSemantics World semD) T ctx { tag := .Prohibition, formula := φ } ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [DeontologicalImperativeTheory.toValueJudgmentTheory, morallyBad, valueSentence, DeonticSentence.toValue, deonticToMoralValue] using
        (entails_map_iff_under
          (sem₁ := deonticSemantics World semD)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := DeonticSentence.toValue)
          (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ tag := .Prohibition, formula := φ } : DeonticSentence World)))
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hObl).1 hEnt⟩
    · rcases hBad with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hProh).1 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hObl).2 hEntGood)
    · rcases hPerm with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hObl).2 hEntGood)
      · intro hEntBad
        exact hNotBad ((hProh).2 hEntBad)
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hObl :
        EntailsUnder (deonticSemantics World semD) T ctx { tag := .Obligation, formula := φ } ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [DeontologicalImperativeTheory.toValueJudgmentTheory, morallyGood, valueSentence, DeonticSentence.toValue,
        deonticToMoralValue] using
        (entails_map_iff_under
          (sem₁ := deonticSemantics World semD)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := DeonticSentence.toValue)
          (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ tag := .Obligation, formula := φ } : DeonticSentence World)))
    have hProh :
        EntailsUnder (deonticSemantics World semD) T ctx { tag := .Prohibition, formula := φ } ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [DeontologicalImperativeTheory.toValueJudgmentTheory, morallyBad, valueSentence, DeonticSentence.toValue, deonticToMoralValue] using
        (entails_map_iff_under
          (sem₁ := deonticSemantics World semD)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := DeonticSentence.toValue)
          (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ tag := .Prohibition, formula := φ } : DeonticSentence World)))
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hObl).2 hEnt⟩
    · rcases hBad with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hProh).2 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hObl).1 hEntGood)
    · rcases hPerm with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hObl).1 hEntGood)
      · intro hEntBad
        exact hNotBad ((hProh).1 hEntBad)

theorem evaluateUtilitarianTheoryUnder_eq_evaluateTheoryUnder_toValue {World : Type u}
    (semU : UtilityAssignmentSemantics World)
    (T : UtilityAssignmentTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    evaluateUtilitarianTheoryUnder (World := World) semU T ctx cp =
      evaluateTheoryUnder (World := World) (valueSemanticsOfUtility World semU) (T.toValueJudgmentTheory) ctx cp := by
  funext s
  apply propext
  constructor <;> intro hs
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hGood :
        EntailsUnder (utilityAssignmentSemantics World semU) T ctx ({ tag := 1, formula := φ } : UtilityAssignmentSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
            (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [UtilityAssignmentTheory.toValueJudgmentTheory, morallyGood, valueSentence, UtilityAssignmentSentence.toValue, utilityToMoralValue] using
        (entails_map_iff_under
          (sem₁ := utilityAssignmentSemantics World semU)
          (sem₂ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (f := UtilityAssignmentSentence.toValue)
          (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
          (T := T) (C := ctx) (s := ({ tag := 1, formula := φ } : UtilityAssignmentSentence World)))
    have hBad :
        EntailsUnder (utilityAssignmentSemantics World semU) T ctx ({ tag := -1, formula := φ } : UtilityAssignmentSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
            (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [UtilityAssignmentTheory.toValueJudgmentTheory, morallyBad, valueSentence, UtilityAssignmentSentence.toValue, utilityToMoralValue] using
        (entails_map_iff_under
          (sem₁ := utilityAssignmentSemantics World semU)
          (sem₂ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (f := UtilityAssignmentSentence.toValue)
          (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
          (T := T) (C := ctx) (s := ({ tag := -1, formula := φ } : UtilityAssignmentSentence World)))
    rcases hCases with h1 | h2 | h3
    · rcases h1 with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hGood).1 hEnt⟩
    · rcases h2 with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hBad).1 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hGood).2 hEntGood)
    · rcases h3 with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hGood).2 hEntGood)
      · intro hEntBad
        exact hNotBad ((hBad).2 hEntBad)
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hGood :
        EntailsUnder (utilityAssignmentSemantics World semU) T ctx ({ tag := 1, formula := φ } : UtilityAssignmentSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
            (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [UtilityAssignmentTheory.toValueJudgmentTheory, morallyGood, valueSentence, UtilityAssignmentSentence.toValue, utilityToMoralValue] using
        (entails_map_iff_under
          (sem₁ := utilityAssignmentSemantics World semU)
          (sem₂ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (f := UtilityAssignmentSentence.toValue)
          (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
          (T := T) (C := ctx) (s := ({ tag := 1, formula := φ } : UtilityAssignmentSentence World)))
    have hBad :
        EntailsUnder (utilityAssignmentSemantics World semU) T ctx ({ tag := -1, formula := φ } : UtilityAssignmentSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
            (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [UtilityAssignmentTheory.toValueJudgmentTheory, morallyBad, valueSentence, UtilityAssignmentSentence.toValue, utilityToMoralValue] using
        (entails_map_iff_under
          (sem₁ := utilityAssignmentSemantics World semU)
          (sem₂ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (f := UtilityAssignmentSentence.toValue)
          (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
          (T := T) (C := ctx) (s := ({ tag := -1, formula := φ } : UtilityAssignmentSentence World)))
    rcases hCases with h1 | h2 | h3
    · rcases h1 with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hGood).2 hEnt⟩
    · rcases h2 with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hBad).2 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hGood).1 hEntGood)
    · rcases h3 with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hGood).1 hEntGood)
      · intro hEntBad
        exact hNotBad ((hBad).1 hEntBad)

theorem evaluateVirtueTargetTheoryUnder_eq_evaluateTheoryUnder_toValue {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (T : VirtueTargetTheory World) (ctx : Formula World) (cp : ChoicePoint World) :
    evaluateVirtueTargetTheoryUnder (World := World) semT T ctx cp =
      evaluateTheoryUnder (World := World) semV (T.toValueJudgmentTheory) ctx cp := by
  funext s
  apply propext
  constructor <;> intro hs
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hGood :
        EntailsUnder (virtueTargetSemantics World semT) T ctx ({ aspect := .Virtuous, formula := φ } : VirtueTargetSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [VirtueTargetTheory.toValueJudgmentTheory, morallyGood, valueSentence, VirtueTargetSentence.toValue,
        virtueAspectToMoralValue] using
        (entails_map_iff_under
          (sem₁ := virtueTargetSemantics World semT)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := VirtueTargetSentence.toValue)
          (h_sat := fun w s => VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ aspect := .Virtuous, formula := φ } : VirtueTargetSentence World)))
    have hBad :
        EntailsUnder (virtueTargetSemantics World semT) T ctx ({ aspect := .Vicious, formula := φ } : VirtueTargetSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [VirtueTargetTheory.toValueJudgmentTheory, morallyBad, valueSentence, VirtueTargetSentence.toValue,
        virtueAspectToMoralValue] using
        (entails_map_iff_under
          (sem₁ := virtueTargetSemantics World semT)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := VirtueTargetSentence.toValue)
          (h_sat := fun w s => VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ aspect := .Vicious, formula := φ } : VirtueTargetSentence World)))
    rcases hCases with h1 | h2 | h3
    · rcases h1 with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hGood).1 hEnt⟩
    · rcases h2 with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hBad).1 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hGood).2 hEntGood)
    · rcases h3 with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hGood).2 hEntGood)
      · intro hEntBad
        exact hNotBad ((hBad).2 hEntBad)
  · rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    have hGood :
        EntailsUnder (virtueTargetSemantics World semT) T ctx ({ aspect := .Virtuous, formula := φ } : VirtueTargetSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyGood φ) := by
      simpa [VirtueTargetTheory.toValueJudgmentTheory, morallyGood, valueSentence, VirtueTargetSentence.toValue,
        virtueAspectToMoralValue] using
        (entails_map_iff_under
          (sem₁ := virtueTargetSemantics World semT)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := VirtueTargetSentence.toValue)
          (h_sat := fun w s => VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ aspect := .Virtuous, formula := φ } : VirtueTargetSentence World)))
    have hBad :
        EntailsUnder (virtueTargetSemantics World semT) T ctx ({ aspect := .Vicious, formula := φ } : VirtueTargetSentence World) ↔
          EntailsUnder (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) ctx (morallyBad φ) := by
      simpa [VirtueTargetTheory.toValueJudgmentTheory, morallyBad, valueSentence, VirtueTargetSentence.toValue,
        virtueAspectToMoralValue] using
        (entails_map_iff_under
          (sem₁ := virtueTargetSemantics World semT)
          (sem₂ := valueJudgmentSemantics World semV)
          (f := VirtueTargetSentence.toValue)
          (h_sat := fun w s => VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
          (T := T) (C := ctx) (s := ({ aspect := .Vicious, formula := φ } : VirtueTargetSentence World)))
    rcases hCases with h1 | h2 | h3
    · rcases h1 with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hGood).2 hEnt⟩
    · rcases h2 with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hBad).2 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hGood).1 hEntGood)
    · rcases h3 with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hGood).1 hEntGood)
      · intro hEntBad
        exact hNotBad ((hBad).1 hEntBad)

end Foet
