import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaMatching

/-!
# Transport of computed equation matches

A successful match commutes with contextual substitution, including repeated
slots and right-side coverage. Failed matching has no corresponding reflection
law: substitution can connect previously distinct variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableSchemaMatching

variable {Head : Type} [DecidableEq Head]

def Assignment.mapSub {slots ambient next : Nat} (substitution : Sub Head ambient next)
    (assignment : Assignment Head slots ambient) : Assignment Head slots next :=
  fun index => (assignment index).map (Presentation.subst substitution)

theorem bindSlot_mapSub {slots ambient next : Nat} {assignment updated : Assignment Head slots ambient}
    {index : Fin slots} {value : Tm Head ambient}
    (computed : bindSlot assignment index value = some updated)
    (substitution : Sub Head ambient next) :
    bindSlot (assignment.mapSub substitution) index (Presentation.subst substitution value) =
      some (updated.mapSub substitution) := by
  cases prior : assignment index with
  | none =>
      simp only [bindSlot, prior] at computed
      cases computed
      have mapped :
          Assignment.mapSub substitution (Function.update assignment index (some value)) =
            Function.update (assignment.mapSub substitution) index
              (some (Presentation.subst substitution value)) := by
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
theorem run_mapSub {slots ambient next : Nat} (pattern : Tm Head slots) :
    ∀ {subject : Tm Head ambient} {assignment updated : Assignment Head slots ambient},
      run pattern subject assignment = some updated →
      ∀ substitution : Sub Head ambient next,
        run pattern (Presentation.subst substitution subject) (assignment.mapSub substitution) =
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
        simp only [Presentation.subst, run, ite_true]
      · cases computed
  | head head =>
      intro subject assignment updated computed substitution
      cases subject <;> simp only [run] at computed <;> try cases computed
      split at computed
      · rename_i same
        cases computed
        subst same
        simp only [Presentation.subst, run, ite_true]
      · cases computed
  | app function argument functionIH argumentIH =>
      intro subject assignment updated computed substitution
      cases subject <;> simp only [run] at computed <;> try cases computed
      rename_i actualFunction actualArgument
      cases initial : run function actualFunction assignment with
      | none => simp only [initial] at computed; cases computed
      | some middle =>
          simp only [initial] at computed
          simp only [Presentation.subst, run, functionIH initial substitution]
          exact argumentIH computed substitution
  | refl subject ih =>
      intro actual assignment updated computed substitution
      cases actual <;> simp only [run] at computed <;> try cases computed
      exact ih computed substitution
  | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | fst _ | snd _ =>
      intro subject assignment updated computed
      cases subject <;> cases computed

omit [DecidableEq Head] in
theorem materialize_mapSub {slots ambient next : Nat} (assignment : Assignment Head slots ambient)
    (substitution : Sub Head ambient next) (index : Fin slots) :
    materialize (assignment.mapSub substitution) index =
      Presentation.subst substitution (materialize assignment index) := by
  cases found : assignment index <;>
    simp only [materialize, Assignment.mapSub, found, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, Presentation.subst]

omit [DecidableEq Head] in
theorem rightAssigned_mapSub {slots ambient next : Nat} {rhs : Tm Head slots}
    {assignment : Assignment Head slots ambient} (assigned : RightAssigned rhs assignment)
    (substitution : Sub Head ambient next) : RightAssigned rhs (assignment.mapSub substitution) := by
  intro index occurs
  have present := assigned index occurs
  cases found : assignment index with
  | none => rw [found] at present; cases present
  | some value => simp only [Assignment.mapSub, found, Option.map_some, Option.isSome_some]

end TypedEquality.Normalization.ExecutableSchemaMatching
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
