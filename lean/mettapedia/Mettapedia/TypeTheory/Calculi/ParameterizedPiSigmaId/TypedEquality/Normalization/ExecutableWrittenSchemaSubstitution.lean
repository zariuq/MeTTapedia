import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenSchemaMatching

/-!
# Transport of computed equation matches

A successful match commutes with contextual substitution, including repeated
slots and right-side coverage. Failed matching has no corresponding reflection
law: substitution can connect previously distinct variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenSchemaMatching

variable {Head : Type} [DecidableEq Head]

def Assignment.mapSub {slots ambient next : Nat} (substitution : ATm.ASub Head ambient next)
    (assignment : Assignment Head slots ambient) : Assignment Head slots next :=
  fun index => (assignment index).map (ATm.subst substitution)

theorem bindSlot_mapSub {slots ambient next : Nat} {assignment updated : Assignment Head slots ambient}
    {index : Fin slots} {value : ATm Head ambient}
    (computed : bindSlot assignment index value = some updated)
    (substitution : ATm.ASub Head ambient next) :
    bindSlot (assignment.mapSub substitution) index (ATm.subst substitution value) =
      some (updated.mapSub substitution) := by
  cases prior : assignment index with
  | none =>
      simp only [bindSlot, prior] at computed
      cases computed
      have mapped :
          Assignment.mapSub substitution (Function.update assignment index (some value)) =
            Function.update (assignment.mapSub substitution) index
              (some (ATm.subst substitution value)) := by
        funext other
        by_cases same : other = index
        · subst other
          simp only [Assignment.mapSub, Function.update_self, Option.map_some]
        · simp only [Assignment.mapSub, Function.update_of_ne same]
      simp only [bindSlot, Assignment.mapSub, prior, Option.map_none]
      exact congrArg some mapped.symm
  | some old =>
      simp only [bindSlot, prior] at computed
      split at computed
      · rename_i same
        cases computed
        subst value
        simp only [bindSlot, Assignment.mapSub, prior, Option.map_some, ite_true]
      · cases computed

/-- Successful execution, rather than only its denotational instance,
commutes with substituting the surrounding context. -/
theorem run_mapSub {slots ambient next : Nat} (pattern : ATm Head slots) :
    ∀ {subject : ATm Head ambient} {assignment updated : Assignment Head slots ambient},
      run pattern subject assignment = some updated →
      ∀ substitution : ATm.ASub Head ambient next,
        run pattern (ATm.subst substitution subject) (assignment.mapSub substitution) =
          some (updated.mapSub substitution) := by
  induction pattern with
  | var index =>
      intro subject assignment updated computed substitution
      exact bindSlot_mapSub computed substitution
  | const name =>
      intro subject assignment updated computed substitution
      cases subject <;> simp only [run] at computed <;> try cases computed
      split at computed
      · rename_i same
        cases computed
        subst same
        simp only [ATm.subst, run, ite_true]
      · cases computed
  | head head =>
      intro subject assignment updated computed substitution
      cases subject <;> simp only [run] at computed <;> try cases computed
      split at computed
      · rename_i same
        cases computed
        subst same
        simp only [ATm.subst, run, ite_true]
      · cases computed
  | app function argument functionIH argumentIH =>
      intro subject assignment updated computed substitution
      cases subject <;> simp only [run] at computed <;> try cases computed
      rename_i actualFunction actualArgument
      cases initial : run function actualFunction assignment with
      | none => simp only [initial] at computed; cases computed
      | some middle =>
          simp only [initial] at computed
          simp only [ATm.subst, run, functionIH initial substitution]
          exact argumentIH computed substitution
  | refl subject ih =>
      intro actual assignment updated computed substitution
      cases actual <;> simp only [run] at computed <;> try cases computed
      exact ih computed substitution
  | pi _ _ | sigma _ _ | id _ _ _ | lamBare _ | lamTyped _ _ | pair _ _ | fst _ | snd _ =>
      intro subject assignment updated computed
      cases subject <;> cases computed

omit [DecidableEq Head] in
theorem materialize_mapSub {slots ambient next : Nat} (assignment : Assignment Head slots ambient)
    (substitution : ATm.ASub Head ambient next) (index : Fin slots) :
    materialize (assignment.mapSub substitution) index =
      ATm.subst substitution (materialize assignment index) := by
  cases found : assignment index <;>
    simp only [materialize, Assignment.mapSub, found, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, ATm.subst]

omit [DecidableEq Head] in
theorem rightAssigned_mapSub {slots ambient next : Nat} {rhs : ATm Head slots}
    {assignment : Assignment Head slots ambient} (assigned : RightAssigned rhs assignment)
    (substitution : ATm.ASub Head ambient next) : RightAssigned rhs (assignment.mapSub substitution) := by
  intro index occurs
  have present := assigned index occurs
  cases found : assignment index with
  | none => rw [found] at present; cases present
  | some value => simp only [Assignment.mapSub, found, Option.map_some, Option.isSome_some]

end TypedEquality.Normalization.ExecutableWrittenSchemaMatching
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
