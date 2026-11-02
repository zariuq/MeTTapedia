import Mettapedia.Languages.Maude.ConditionalMaxValue
import Mathlib.Data.List.Nodup

/-! Every successful closed max-expression observation is justified by
the actual source equations. The observer is not the emitted executor.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.ConditionalMax

def successorFrame : ArgumentContext Examples.conditional.signature [] "Nat" "Nat" :=
  ⟨successorOperator, successor_member, [], [], [], [], rfl, rfl, .nil, .nil⟩

theorem observed_value_equivalent (source : Term) (value : Nat)
    (observed : value? source = some value)
    (typed : HasSort Examples.conditional.signature [] source "Nat") :
    Equivalent Examples.conditional [] "Nat" source (numeral value) := by
  revert value observed typed
  refine Term.rec
    (motive_1 := fun source => ∀ value, value? source = some value →
      HasSort Examples.conditional.signature [] source "Nat" →
      Equivalent Examples.conditional [] "Nat" source (numeral value))
    (motive_2 := fun sources => ∀ source ∈ sources, ∀ value, value? source = some value →
      HasSort Examples.conditional.signature [] source "Nat" →
      Equivalent Examples.conditional [] "Nat" source (numeral value))
    ?_ ?_ ?_ ?_ source
  · intro name value impossible _
    simp [value?] at impossible
  · intro label arguments ih value observed typed
    unfold value? at observed
    split at observed
    · rename_i shape
      obtain ⟨rfl, rfl⟩ := Term.app.inj shape
      cases Option.some.inj observed
      exact .refl (numeral_sorted [] 0)
    · rename_i child shape
      obtain ⟨rfl, rfl⟩ := Term.app.inj shape
      obtain ⟨actual, childObserved, valueSame⟩ := Option.map_eq_some_iff.mp observed
      cases valueSame
      obtain ⟨declaration, member, labelSame, _, argumentsTyped⟩ := HasSort.operator_arguments typed rfl
      have declarationSame : declaration = successorOperator := by
        have unique : (Examples.conditional.signature.operators.map Operator.id).Nodup := by decide_cbv
        exact List.inj_on_of_nodup_map unique member successor_member labelSame
      subst declaration
      cases argumentsTyped with
      | cons childTyped _ =>
        have childMeaning := ih child List.mem_cons_self actual childObserved childTyped
        simpa only [successorFrame, ArgumentContext.plug, successorOperator, List.nil_append,
          numeral, Examples.numeral, String.reduceAppend] using Equivalent.argument successorFrame childMeaning
    · rename_i left right shape
      obtain ⟨rfl, rfl⟩ := Term.app.inj shape
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at observed
      obtain ⟨first, firstObserved, second, secondObserved, valueSame⟩ := observed
      cases valueSame
      obtain ⟨declaration, member, labelSame, _, argumentsTyped⟩ := HasSort.operator_arguments typed rfl
      have declarationSame : declaration = maxOperator := by
        have unique : (Examples.conditional.signature.operators.map Operator.id).Nodup := by decide_cbv
        exact List.inj_on_of_nodup_map unique member max_member labelSame
      subst declaration
      cases argumentsTyped with
      | cons firstTyped tail =>
        cases tail with
        | cons secondTyped _ =>
          exact .trans (maximum_congruent (ih left List.mem_cons_self first firstObserved firstTyped)
            (ih right (by simp) second secondObserved secondTyped)) (maximum_equivalent first second)
    · cases observed
  · intro term impossible
    cases impossible
  · intro first rest firstIH restIH term member value observed typed
    rcases List.mem_cons.mp member with rfl | member
    · exact firstIH value observed typed
    · exact restIH term member value observed typed

#print axioms observed_value_equivalent

end Mettapedia.Languages.Maude.ConditionalMax
