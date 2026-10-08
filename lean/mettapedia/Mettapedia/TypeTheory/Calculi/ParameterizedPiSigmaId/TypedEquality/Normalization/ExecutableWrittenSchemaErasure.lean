import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenSchemaSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaMatching

/-!
# Erasure preserves successful source matching

Captures retain complete written terms. Erasing a successful match gives a
successful erased match, including every shared slot. Its converse fails when
repeated captures have different annotations. Right-side instantiation
commutes with erasure through the complete scoped substitution algebra.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenSchemaMatching

variable {Head : Type} [DecidableEq Head]

def Assignment.erase {slots ambient : Nat} (assignment : Assignment Head slots ambient) :
    ExecutableSchemaMatching.Assignment Head slots ambient :=
  fun index => (assignment index).map ATm.erase

theorem bindSlot_erase {slots ambient : Nat} {assignment updated : Assignment Head slots ambient}
    {index : Fin slots} {value : ATm Head ambient}
    (computed : bindSlot assignment index value = some updated) :
    ExecutableSchemaMatching.bindSlot assignment.erase index value.erase = some updated.erase := by
  cases prior : assignment index with
  | none =>
      simp only [bindSlot, prior] at computed
      cases computed
      have mapped :
          Assignment.erase (Function.update assignment index (some value)) =
            Function.update assignment.erase index (some value.erase) := by
        funext other
        by_cases same : other = index
        · subst other
          simp only [Assignment.erase, Function.update_self, Option.map_some]
        · simp only [Assignment.erase, Function.update_of_ne same]
      simp only [ExecutableSchemaMatching.bindSlot, Assignment.erase, prior, Option.map_none]
      exact congrArg some mapped.symm
  | some old =>
      simp only [bindSlot, prior] at computed
      split at computed
      · rename_i same
        cases computed
        subst value
        simp only [ExecutableSchemaMatching.bindSlot, Assignment.erase, prior,
          Option.map_some, ite_true]
      · cases computed

/-- Full written equality implies equality after erasure; the executable
matcher transports that implication rather than replacing its equality test. -/
theorem run_erase {slots ambient : Nat} (pattern : ATm Head slots) :
    ∀ {subject : ATm Head ambient} {assignment updated : Assignment Head slots ambient},
      run pattern subject assignment = some updated →
      ExecutableSchemaMatching.run pattern.erase subject.erase assignment.erase = some updated.erase := by
  induction pattern with
  | var index =>
      intro subject assignment updated computed
      exact bindSlot_erase computed
  | const name =>
      intro subject assignment updated computed
      cases subject <;> simp only [run] at computed <;> try cases computed
      split at computed
      · rename_i same
        cases computed
        subst same
        simp only [ATm.erase, ExecutableSchemaMatching.run, ite_true]
      · cases computed
  | head head =>
      intro subject assignment updated computed
      cases subject <;> simp only [run] at computed <;> try cases computed
      split at computed
      · rename_i same
        cases computed
        subst same
        simp only [ATm.erase, ExecutableSchemaMatching.run, ite_true]
      · cases computed
  | app function argument functionIH argumentIH =>
      intro subject assignment updated computed
      cases subject <;> simp only [run] at computed <;> try cases computed
      rename_i actualFunction actualArgument
      cases initial : run function actualFunction assignment with
      | none => simp only [initial] at computed; cases computed
      | some middle =>
          simp only [initial] at computed
          simp only [ATm.erase, ExecutableSchemaMatching.run, functionIH initial]
          exact argumentIH computed
  | refl subject ih =>
      intro actual assignment updated computed
      cases actual <;> simp only [run] at computed <;> try cases computed
      exact ih computed
  | pi _ _ | sigma _ _ | id _ _ _ | lamBare _ | lamTyped _ _ | pair _ _ | fst _ | snd _ =>
      intro subject assignment updated computed
      cases subject <;> cases computed

omit [DecidableEq Head] in
theorem materialize_erase {slots ambient : Nat} (assignment : Assignment Head slots ambient) :
    ATm.eraseSub (materialize assignment) = ExecutableSchemaMatching.materialize assignment.erase := by
  funext index
  cases found : assignment index <;>
    simp only [ATm.eraseSub, ATm.erase, materialize, ExecutableSchemaMatching.materialize,
      Assignment.erase, found, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]

omit [DecidableEq Head] in
theorem target_erase {slots ambient : Nat} (assignment : Assignment Head slots ambient)
    (right : ATm Head slots) :
    (ATm.subst (materialize assignment) right).erase =
      Presentation.subst (ExecutableSchemaMatching.materialize assignment.erase) right.erase := by
  rw [ATm.erase_subst, materialize_erase]

end TypedEquality.Normalization.ExecutableWrittenSchemaMatching
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
