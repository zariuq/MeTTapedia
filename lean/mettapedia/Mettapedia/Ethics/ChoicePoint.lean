import Mettapedia.Ethics.Core
import Mettapedia.Ethics.UtilitarianToValue
import Mettapedia.Ethics.UtilitarianToVirtue
import Mettapedia.Ethics.VirtueToValue

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u

/-- A choice point is a set of alternative action formulas. -/
abbrev ChoicePoint (World : Type u) : Type u :=
  Set (Formula World)

def ValueMoralDilemma {World : Type u}
    (semV : ValueSemantics World) (w : World) (cp : ChoicePoint World) : Prop :=
  ∀ φ, φ ∈ cp → semV.morally .MorallyBad φ w

def DeonticMoralDilemma {World : Type u}
    (semD : DeonticSemantics World) (w : World) (cp : ChoicePoint World) : Prop :=
  ∀ φ, φ ∈ cp → semD.deontic .Prohibition φ w

def UtilitarianMoralDilemma {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World) (cp : ChoicePoint World) : Prop :=
  ∀ φ, φ ∈ cp → semU.utility w φ < 0

def VirtueTargetMoralDilemma {World : Type u}
    (semT : VirtueTargetSemantics World) (w : World) (cp : ChoicePoint World) : Prop :=
  ∀ φ, φ ∈ cp → semT.targets .Vicious φ w

theorem deonticMoralDilemma_iff_valueMoralDilemma {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) (cp : ChoicePoint World) :
    DeonticMoralDilemma semD w cp ↔ ValueMoralDilemma semV w cp := by
  constructor
  · intro h φ hφ
    have hd : semD.deontic .Prohibition φ w := h φ hφ
    simpa [deonticToMoralValue] using (h_align .Prohibition φ w).1 hd
  · intro h φ hφ
    have hv : semV.morally .MorallyBad φ w := h φ hφ
    simpa [deonticToMoralValue] using (h_align .Prohibition φ w).2 hv

theorem utilitarianMoralDilemma_iff_valueMoralDilemma {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World) (cp : ChoicePoint World) :
    UtilitarianMoralDilemma semU w cp ↔
      ValueMoralDilemma (valueSemanticsOfUtility World semU) w cp := by
  constructor
  · intro h φ hφ
    have hu : semU.utility w φ < 0 := h φ hφ
    simpa [ValueMoralDilemma, valueSemanticsOfUtility] using hu
  · intro h φ hφ
    have hv : (valueSemanticsOfUtility World semU).morally .MorallyBad φ w := h φ hφ
    simpa [valueSemanticsOfUtility] using hv

theorem utilitarianMoralDilemma_iff_virtueTargetMoralDilemma {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World) (cp : ChoicePoint World) :
    UtilitarianMoralDilemma semU w cp ↔
      VirtueTargetMoralDilemma (virtueTargetSemanticsOfUtility World semU) w cp := by
  constructor
  · intro h φ hφ
    have hu : semU.utility w φ < 0 := h φ hφ
    simpa [VirtueTargetMoralDilemma, virtueTargetSemanticsOfUtility, virtueAspectToMoralValue] using hu
  · intro h φ hφ
    have hv : (virtueTargetSemanticsOfUtility World semU).targets .Vicious φ w := h φ hφ
    simpa [virtueTargetSemanticsOfUtility, virtueAspectToMoralValue] using hv

end Mettapedia.Ethics
