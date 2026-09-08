import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeRelatorEliminationPreservation

/-!
# Selected-index and selected-evidence relator controls

A typed substitution replaces both list tails and their relational evidence
together. The actual endpoints remain admitted in the original open context.
Redirecting only the recursive evidence is not the installed root step.
These negative controls distinguish raw root evidence and displayed syntax;
they do not assert failure of whole-profile conversion or arbitrary typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeRelatorElimination
namespace Examples

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open IntrinsicRelator
open FormationSensitiveNativeList (Typing)

def nilTailsSubstitution : Sub Tower.Head 12 12 :=
  consSchemaSubstitution (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
    (.var 5) (.var 4) (Intrinsic.nilApp (.var 11)) (Intrinsic.nilApp (.var 10))
    (.var 1) (nilRelApp (.var 11) (.var 10) (.var 9))

theorem nilTailsSubstitution_typed :
    FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail nilTailsSubstitution := by
  apply consSchema_typed
  · intro index
    fin_cases index <;> exact FormationSensitive.Typing.var _
  · exact FormationSensitive.Typing.var 5
  · exact FormationSensitive.Typing.var 4
  · exact FormationSensitiveNativeList.nilApp_hasType (FormationSensitive.Typing.var 11)
  · exact FormationSensitiveNativeList.nilApp_hasType (FormationSensitive.Typing.var 10)
  · exact FormationSensitive.Typing.var 1
  · exact FormationSensitiveNativeList.nilRelApp_hasType
      (FormationSensitive.Typing.var 11) (FormationSensitive.Typing.var 10)
      (FormationSensitive.Typing.var 9)

def nilTailsSource : Tower.Tm 12 :=
  eliminateApp (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
    (Intrinsic.consApp (.var 11) (.var 5) (Intrinsic.nilApp (.var 11)))
    (Intrinsic.consApp (.var 10) (.var 4) (Intrinsic.nilApp (.var 10)))
    (consRelApp (.var 11) (.var 10) (.var 9) (.var 5) (.var 4)
      (Intrinsic.nilApp (.var 11)) (Intrinsic.nilApp (.var 10)) (.var 1)
      (nilRelApp (.var 11) (.var 10) (.var 9)))

def nilTailsTarget : Tower.Tm 12 :=
  .app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4))
    (Intrinsic.nilApp (.var 11))) (Intrinsic.nilApp (.var 10))) (.var 1))
    (nilRelApp (.var 11) (.var 10) (.var 9)))
    (eliminateApp (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (Intrinsic.nilApp (.var 11)) (Intrinsic.nilApp (.var 10))
      (nilRelApp (.var 11) (.var 10) (.var 9)))

def nilTailsResult : Tower.Tm 12 :=
  motiveApp (.var 8)
    (Intrinsic.consApp (.var 11) (.var 5) (Intrinsic.nilApp (.var 11)))
    (Intrinsic.consApp (.var 10) (.var 4) (Intrinsic.nilApp (.var 10)))
    (consRelApp (.var 11) (.var 10) (.var 9) (.var 5) (.var 4)
      (Intrinsic.nilApp (.var 11)) (Intrinsic.nilApp (.var 10)) (.var 1)
      (nilRelApp (.var 11) (.var 10) (.var 9)))

theorem selected_nilTails_judgments :
    FormationSensitive.Judgment rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail nilTailsSource nilTailsResult ∧
    FormationSensitive.Judgment rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail nilTailsTarget nilTailsResult :=
  consIota_substitute consContext_formed nilTailsSubstitution_typed

theorem selected_nilTails_root : rules.computation.step nilTailsSource nilTailsTarget :=
  consIota_substitutedRoot nilTailsSubstitution

/-- The original branch and its six payloads are unchanged; only the
recursive call is redirected from the selected tail witness to the head witness. -/
def redirectedRecursiveEvidence : Tower.Tm 12 :=
  .app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4))
    (.var 3)) (.var 2)) (.var 1)) (.var 0))
    (eliminateApp (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (.var 3) (.var 2) (.var 1))

private theorem relator_iota_target_unique {n : Nat} {left first second : Tower.Tm n}
    (one : IotaEvidence n left first) (two : IotaEvidence n left second) : first = second := by
  cases one <;> cases two <;> rfl

theorem redirected_recursiveEvidence_not_relatorIota :
    ¬ Nonempty (IotaEvidence 12 consIotaLeft redirectedRecursiveEvidence) := by
  rintro ⟨altered⟩
  have original : IotaEvidence 12 consIotaLeft consIotaRight :=
    .cons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
  have same := relator_iota_target_unique original altered
  exact (by decide : consIotaRight ≠ redirectedRecursiveEvidence) same

theorem redirected_recursiveEvidence_not_root :
    ¬ rules.computation.step consIotaLeft redirectedRecursiveEvidence := by
  intro step
  cases step with
  | inherited impossible => exact impossible.elim
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence => cases evidence
      | rel evidence => exact redirected_recursiveEvidence_not_relatorIota ⟨evidence⟩

theorem changed_tails_change_displayed_result : nilTailsResult ≠ consIotaResultType := by decide

/-- Even with both list indices fixed, the declared motive receives the
actual evidence term as its third argument. -/
theorem changed_evidence_changes_displayed_result :
    consIotaResultType ≠
      motiveApp (.var 8)
        (Intrinsic.consApp (.var 11) (.var 5) (.var 3))
        (Intrinsic.consApp (.var 10) (.var 4) (.var 2))
        (consRelApp (.var 11) (.var 10) (.var 9) (.var 5) (.var 4)
          (.var 3) (.var 2) (.var 1) (.var 1)) := by decide

#print axioms nilTailsSubstitution_typed
#print axioms selected_nilTails_judgments
#print axioms selected_nilTails_root
#print axioms redirected_recursiveEvidence_not_relatorIota
#print axioms redirected_recursiveEvidence_not_root
#print axioms changed_tails_change_displayed_result
#print axioms changed_evidence_changes_displayed_result

end Examples
end FormationSensitiveNativeRelatorElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
