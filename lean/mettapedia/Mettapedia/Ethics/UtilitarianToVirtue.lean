import Mettapedia.Ethics.UtilitarianToValue
import Mettapedia.Ethics.VirtueToValue

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u

/-- Utility-assignment sentence → virtue-target sentence (via value judgments). -/
def UtilityAssignmentSentence.toVirtueTarget {World : Type u}
    (s : UtilityAssignmentSentence World) :
    VirtueTargetSentence World :=
  s.toValue.toVirtueTarget

def UtilityAssignmentTheory.toVirtueTargetTheory {World : Type u}
    (T : UtilityAssignmentTheory World) :
    VirtueTargetTheory World :=
  Theory.map UtilityAssignmentSentence.toVirtueTarget T

/-- Virtue-target semantics induced by a utility function. -/
def virtueTargetSemanticsOfUtility (World : Type u)
    (semU : UtilityAssignmentSemantics World) : VirtueTargetSemantics World :=
  ⟨fun aspect φ w =>
    match virtueAspectToMoralValue aspect with
    | .MorallyGood => semU.utility w φ > 0
    | .MorallyBad => semU.utility w φ < 0
    | .MorallyPermissible => semU.utility w φ = 0⟩

theorem UtilityAssignmentSemantics.sat_iff_sat_toVirtueTarget {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World)
    (s : UtilityAssignmentSentence World) :
    (utilityAssignmentSemantics World semU).Sat w s ↔
      (virtueTargetSemantics World (virtueTargetSemanticsOfUtility World semU)).Sat w
        s.toVirtueTarget := by
  cases s with
  | mk tag formula =>
      dsimp [UtilityAssignmentSentence.toVirtueTarget, UtilityAssignmentSentence.toValue,
        ValueJudgmentSentence.toVirtueTarget, utilityAssignmentSemantics, virtueTargetSemantics,
        UtilityAssignmentSemantics.sat, VirtueTargetSemantics.sat, virtueTargetSemanticsOfUtility]
      simp [virtueAspectToMoralValue_moralValueToVirtueAspect]
      rfl

theorem entails_utilitarian_iff_entails_virtueTarget {World : Type u}
    (semU : UtilityAssignmentSemantics World)
    (T : UtilityAssignmentTheory World) (s : UtilityAssignmentSentence World) :
    Entails (utilityAssignmentSemantics World semU) T s ↔
      Entails
        (virtueTargetSemantics World (virtueTargetSemanticsOfUtility World semU))
        (T.toVirtueTargetTheory) s.toVirtueTarget := by
  simpa [UtilityAssignmentTheory.toVirtueTargetTheory] using
    (entails_map_iff
      (sem₁ := utilityAssignmentSemantics World semU)
      (sem₂ := virtueTargetSemantics World (virtueTargetSemanticsOfUtility World semU))
      (f := UtilityAssignmentSentence.toVirtueTarget)
      (h_sat := fun w s => UtilityAssignmentSemantics.sat_iff_sat_toVirtueTarget (semU := semU) w s)
      (T := T) (s := s))

end Mettapedia.Ethics
