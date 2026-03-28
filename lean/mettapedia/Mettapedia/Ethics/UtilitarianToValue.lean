import Mettapedia.Ethics.Core
import Mettapedia.Ethics.Theory

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u

/-- Interpret an integer utility as a moral value by sign. -/
def utilityToMoralValue (value : Int) : MoralValueAttribute :=
  if value > 0 then
    .MorallyGood
  else if value < 0 then
    .MorallyBad
  else
    .MorallyPermissible

/-- Canonical injection of moral values into utilities. -/
def moralValueToUtility : MoralValueAttribute → Int
  | .MorallyGood => 1
  | .MorallyBad => -1
  | .MorallyPermissible => 0

theorem utilityToMoralValue_moralValueToUtility (m : MoralValueAttribute) :
    utilityToMoralValue (moralValueToUtility m) = m := by
  cases m <;> rfl

/-- A simple utility-assignment sentence: an integer utility attached to a formula. -/
abbrev UtilityAssignmentSentence (World : Type u) : Type (max u 1) :=
  ModalSentence World Int

abbrev UtilityAssignmentTheory (World : Type u) : Type (max u 1) :=
  Theory (UtilityAssignmentSentence World)

/-- Utility assignment sentence → value-judgment sentence. -/
def UtilityAssignmentSentence.toValue {World : Type u}
    (s : UtilityAssignmentSentence World) : ValueJudgmentSentence World :=
  { tag := utilityToMoralValue s.tag, formula := s.formula }

def UtilityAssignmentTheory.toValueJudgmentTheory {World : Type u}
    (T : UtilityAssignmentTheory World) : ValueJudgmentTheory World :=
  Theory.map UtilityAssignmentSentence.toValue T

/-- A semantics for utility assignment sentences, parameterized by a world-relative utility function. -/
structure UtilityAssignmentSemantics (World : Type u) : Type (max u 1) where
  utility : World → Formula World → Int

def UtilityAssignmentSemantics.sat {World : Type u}
    (sem : UtilityAssignmentSemantics World)
    (w : World) (s : UtilityAssignmentSentence World) : Prop :=
  match utilityToMoralValue s.tag with
  | .MorallyGood => sem.utility w s.formula > 0
  | .MorallyBad => sem.utility w s.formula < 0
  | .MorallyPermissible => sem.utility w s.formula = 0

def utilityAssignmentSemantics (World : Type u)
    (sem : UtilityAssignmentSemantics World) :
    Semantics (UtilityAssignmentSentence World) World :=
  ⟨fun w s => UtilityAssignmentSemantics.sat sem w s⟩

/-- Value-judgment semantics induced by the same utility function. -/
def valueSemanticsOfUtility (World : Type u)
    (sem : UtilityAssignmentSemantics World) : ValueSemantics World :=
  ⟨fun attr φ w =>
    match attr with
    | .MorallyGood => sem.utility w φ > 0
    | .MorallyBad => sem.utility w φ < 0
    | .MorallyPermissible => sem.utility w φ = 0⟩

/-- Value-judgment sentence → utility-assignment sentence (canonical constants). -/
def ValueJudgmentSentence.toUtilityAssignment {World : Type u}
    (s : ValueJudgmentSentence World) : UtilityAssignmentSentence World :=
  { tag := moralValueToUtility s.tag, formula := s.formula }

def ValueJudgmentTheory.toUtilityAssignmentTheory {World : Type u}
    (T : ValueJudgmentTheory World) : UtilityAssignmentTheory World :=
  Theory.map ValueJudgmentSentence.toUtilityAssignment T

theorem ValueJudgmentSentence.toUtilityAssignment_toValue {World : Type u}
    (s : ValueJudgmentSentence World) :
    s.toUtilityAssignment.toValue = s := by
  cases s with
  | mk tag formula =>
      simp [ValueJudgmentSentence.toUtilityAssignment, UtilityAssignmentSentence.toValue,
        utilityToMoralValue_moralValueToUtility]

theorem UtilityAssignmentSemantics.sat_iff_sat_toValue {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World)
    (s : UtilityAssignmentSentence World) :
    (utilityAssignmentSemantics World semU).Sat w s ↔
      (valueJudgmentSemantics World (valueSemanticsOfUtility World semU)).Sat w s.toValue := by
  rfl

theorem ValueJudgmentSentence.sat_iff_sat_toUtilityAssignment {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World)
    (s : ValueJudgmentSentence World) :
    (valueJudgmentSemantics World (valueSemanticsOfUtility World semU)).Sat w s ↔
      (utilityAssignmentSemantics World semU).Sat w s.toUtilityAssignment := by
  cases s with
  | mk tag formula =>
      cases tag <;> rfl

theorem entails_utilitarian_iff_entails_value {World : Type u}
    (semU : UtilityAssignmentSemantics World)
    (T : UtilityAssignmentTheory World) (s : UtilityAssignmentSentence World) :
    Entails (utilityAssignmentSemantics World semU) T s ↔
      Entails (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
        (T.toValueJudgmentTheory) s.toValue := by
  simpa [UtilityAssignmentTheory.toValueJudgmentTheory] using
    (entails_map_iff
      (sem₁ := utilityAssignmentSemantics World semU)
      (sem₂ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
      (f := UtilityAssignmentSentence.toValue)
      (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
      (T := T) (s := s))

theorem entails_value_iff_entails_utilitarian {World : Type u}
    (semU : UtilityAssignmentSemantics World)
    (T : ValueJudgmentTheory World) (s : ValueJudgmentSentence World) :
    Entails (valueJudgmentSemantics World (valueSemanticsOfUtility World semU)) T s ↔
      Entails (utilityAssignmentSemantics World semU) (T.toUtilityAssignmentTheory) s.toUtilityAssignment := by
  simpa [ValueJudgmentTheory.toUtilityAssignmentTheory] using
    (entails_map_iff
      (sem₁ := valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
      (sem₂ := utilityAssignmentSemantics World semU)
      (f := ValueJudgmentSentence.toUtilityAssignment)
      (h_sat := fun w s => ValueJudgmentSentence.sat_iff_sat_toUtilityAssignment (semU := semU) w s)
      (T := T) (s := s))

end Mettapedia.Ethics
