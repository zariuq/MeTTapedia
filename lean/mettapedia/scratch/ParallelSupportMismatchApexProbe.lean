import ParallelSupportMismatchApexCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelSupportMismatchApexCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open ParallelSupportMismatchStopCanary

noncomputable def leftExposedOccurrence :
    CostStaticFVarOccurrence leftView.node.plan.abstractPattern where
  name := leftExposedName
  context := .collection rhoReflectivePresentation.parallelCollection []
    (.apply "PDrop" [] .hole [])
    [.apply "PDrop"
      [.apply "NQuote" [.apply "PDrop" [.fvar leftSealedName]]]] none
  selected := by
    rw [leftAbstract_shape]
    exact .collection (.apply .here)

noncomputable def leftSealedOccurrence :
    CostStaticFVarOccurrence leftView.node.plan.abstractPattern where
  name := leftSealedName
  context := .collection rhoReflectivePresentation.parallelCollection
    [.apply "PDrop" [.fvar leftExposedName]]
    (.apply "PDrop" [] (.apply "NQuote" []
      (.apply "PDrop" [] .hole []) []) []) [] none
  selected := by
    rw [leftAbstract_shape]
    exact .collection (.apply (.apply (.apply .here)))

noncomputable def rightSealedOccurrence :
    CostStaticFVarOccurrence rightView.node.plan.abstractPattern where
  name := rightSealedName
  context := .collection rhoReflectivePresentation.parallelCollection []
    (.apply "PDrop" [] (.apply "NQuote" []
      (.apply "PDrop" [] .hole []) []) [])
    [.apply "PDrop" [.fvar rightExposedName]] none
  selected := by
    rw [rightAbstract_shape]
    exact .collection (.apply (.apply (.apply .here)))

noncomputable def rightExposedOccurrence :
    CostStaticFVarOccurrence rightView.node.plan.abstractPattern where
  name := rightExposedName
  context := .collection rhoReflectivePresentation.parallelCollection
    [.apply "PDrop"
      [.apply "NQuote" [.apply "PDrop" [.fvar rightSealedName]]]]
    (.apply "PDrop" [] .hole []) [] none
  selected := by
    rw [rightAbstract_shape]
    exact .collection (.apply .here)

theorem leftExposedSlot_exists :
    (leftEnvironment.slotOfName? leftExposedName).isSome = true :=
  leftEnvironment.slotOfName?_isSome_of_occurrence leftExposedOccurrence

theorem leftSealedSlot_exists :
    (leftEnvironment.slotOfName? leftSealedName).isSome = true :=
  leftEnvironment.slotOfName?_isSome_of_occurrence leftSealedOccurrence

theorem rightSealedSlot_exists :
    (rightEnvironment.slotOfName? rightSealedName).isSome = true :=
  rightEnvironment.slotOfName?_isSome_of_occurrence rightSealedOccurrence

theorem rightExposedSlot_exists :
    (rightEnvironment.slotOfName? rightExposedName).isSome = true :=
  rightEnvironment.slotOfName?_isSome_of_occurrence rightExposedOccurrence

noncomputable def leftExposedSlot : Fin leftEnvironment.atomCount :=
  (leftEnvironment.slotOfName? leftExposedName).get leftExposedSlot_exists

noncomputable def leftSealedSlot : Fin leftEnvironment.atomCount :=
  (leftEnvironment.slotOfName? leftSealedName).get leftSealedSlot_exists

noncomputable def rightSealedSlot : Fin rightEnvironment.atomCount :=
  (rightEnvironment.slotOfName? rightSealedName).get rightSealedSlot_exists

noncomputable def rightExposedSlot : Fin rightEnvironment.atomCount :=
  (rightEnvironment.slotOfName? rightExposedName).get rightExposedSlot_exists

example :
    (leftEnvironment.atomValue leftExposedSlot).key =
      (rightEnvironment.atomValue rightExposedSlot).key := by
  decide

example :
    (leftEnvironment.atomValue leftSealedSlot).key =
      (rightEnvironment.atomValue rightSealedSlot).key := by
  decide

example :
    (leftEnvironment.atomValue leftExposedSlot).key ≠
      (rightEnvironment.atomValue rightSealedSlot).key := by
  decide

end ParallelSupportMismatchApexCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
