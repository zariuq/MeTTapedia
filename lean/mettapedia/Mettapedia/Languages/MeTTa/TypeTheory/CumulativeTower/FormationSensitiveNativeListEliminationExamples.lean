import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListEliminationPreservation

/-!
# Selected-tail controls for refined native List elimination

A genuine typed substitution replaces the open tail by native nil. Both
dependent endpoint judgments and the actual root follow. Redirecting the
recursive call while keeping the original redex is not one of the installed
root computations. This is a root-receipt distinction, not a claim that the
altered term is untypable or nonconvertible under the whole rule package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeListElimination
namespace Examples

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open Intrinsic
open FormationSensitiveNativeList (Typing)

/-- The six-variable open context keeps its tail variable, but this
particular elimination instance selects an independently admitted nil. -/
def nilTailSubstitution : Sub Tower.Head 6 6 :=
  consSchemaSubstitution (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)
    (nilApp (.var 5))

theorem nilTailSubstitution_typed :
    FormationSensitive.CtxMor IntrinsicRelator.rules
      contextAPZSHeadTail contextAPZSHeadTail nilTailSubstitution := by
  apply consSchema_typed
  · intro index
    fin_cases index <;> exact FormationSensitive.Typing.var _
  · exact FormationSensitive.Typing.var 1
  · exact FormationSensitiveNativeList.nilApp_hasType (FormationSensitive.Typing.var 5)

def nilTailSource : Tower.Tm 6 :=
  eliminateApp (.var 5) (.var 4) (.var 3) (.var 2)
    (consApp (.var 5) (.var 1) (nilApp (.var 5)))

def nilTailTarget : Tower.Tm 6 :=
  .app (.app (.app (.var 2) (.var 1)) (nilApp (.var 5)))
    (eliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (nilApp (.var 5)))

def nilTailResult : Tower.Tm 6 :=
  .app (.var 4) (consApp (.var 5) (.var 1) (nilApp (.var 5)))

theorem selected_nilTail_judgments :
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZSHeadTail
      nilTailSource nilTailResult ∧
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZSHeadTail
      nilTailTarget nilTailResult :=
  consIota_substitute contextAPZSHeadTail_formed nilTailSubstitution_typed

theorem selected_nilTail_root :
    IntrinsicRelator.rules.computation.step nilTailSource nilTailTarget :=
  consIota_substitutedRoot nilTailSubstitution

/-- This changes only the recursive argument of the original open cons
reduct, while retaining the original branch and tail arguments. -/
def redirectedRecursiveCall : Tower.Tm 6 :=
  .app (.app (.app (.var 2) (.var 1)) (.var 0))
    (.app eliminateAtConsParameters (nilApp (.var 5)))

private theorem list_iota_target_unique {n : Nat} {left first second : Tower.Tm n}
    (one : Intrinsic.IotaEvidence n left first)
    (two : Intrinsic.IotaEvidence n left second) : first = second := by
  cases one <;> cases two <;> rfl

theorem changed_tail_changes_result :
    nilTailResult ≠ consIotaResultType := by decide

theorem redirected_recursiveCall_not_nativeListIota :
    ¬ Nonempty (Intrinsic.IotaEvidence 6 consIotaLeft redirectedRecursiveCall) := by
  rintro ⟨altered⟩
  have same := list_iota_target_unique consIotaReceipt.evidence altered
  exact (by decide : consIotaRight ≠ redirectedRecursiveCall) same

theorem redirected_recursiveCall_not_root :
    ¬ IntrinsicRelator.rules.computation.step consIotaLeft redirectedRecursiveCall := by
  intro step
  cases step with
  | inherited impossible => exact impossible.elim
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence => exact redirected_recursiveCall_not_nativeListIota ⟨evidence⟩
      | rel evidence => cases evidence

#print axioms nilTailSubstitution_typed
#print axioms selected_nilTail_judgments
#print axioms selected_nilTail_root
#print axioms changed_tail_changes_result
#print axioms redirected_recursiveCall_not_nativeListIota
#print axioms redirected_recursiveCall_not_root

end Examples
end FormationSensitiveNativeListElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
