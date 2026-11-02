import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSubstitution
import Mettapedia.GSLT.LanguageDef.ContextualABTPrefixApplication

/-!
# Sequential opening implements simultaneous contextual application

Before opening the first parameter, its argument is moved past the remaining
parameters. The prefix-application composition law then proves that repeating
this operation gives the simultaneous graft, including reordered or repeated
arguments. These laws justify reuse of the existing shared-store opening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.GraftSemantics

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open ContextualPatterns

variable {Head : Type}

theorem lift_zero_comp (first second : Nat) (term : Term Head) :
    Term.lift 0 first (Term.lift 0 second term) = Term.lift 0 (second + first) term := by
  rw [lift_zero_eq_renameMany, lift_zero_eq_renameMany, lift_zero_eq_renameMany,
    Term.renameMany_comp]
  congr 1
  funext i
  omega

def singleEnvironment (depth : Nat) (replacement : Term Head) (index : Nat) : Term Head :=
  Term.instantiateAt depth replacement (.idx index)

theorem singleEnvironment_under (depth binders : Nat) (replacement : Term Head) :
    underBinders binders (singleEnvironment depth replacement) =
      singleEnvironment (depth + binders) replacement := by
  funext index
  rw [underBinders_eq]
  by_cases inner : index < binders
  · have below : index < depth + binders := by omega
    simp [inner, singleEnvironment, Term.instantiateAt, below]
  · have above : binders ≤ index := by omega
    rcases lt_trichotomy (index - binders) depth with before | atParameter | after
    · have below : index < depth + binders := by omega
      simp [inner, singleEnvironment, Term.instantiateAt, before, below, Term.lift]
      omega
    · have position : index = depth + binders := by omega
      subst index
      simp [singleEnvironment, Term.instantiateAt, inner, lift_zero_comp]
    · have notBefore : ¬index - binders < depth := by omega
      have notEqual : index - binders ≠ depth := by omega
      have notBelow : ¬index < depth + binders := by omega
      have notPosition : index ≠ depth + binders := by omega
      simp [inner, singleEnvironment, Term.instantiateAt, notBefore, notEqual,
        notBelow, notPosition, Term.lift]
      omega

mutual
theorem instantiateAt_parallel (depth : Nat) (replacement body : Term Head) :
    Term.instantiateAt depth replacement body =
      Term.substituteMany (singleEnvironment depth replacement) body := by
  cases body with
  | idx i => rw [Term.substituteMany_idx]; rfl
  | node head fields =>
    rw [Term.instantiateAt, substitute_node, instantiateFieldsAt_parallel depth replacement fields]

theorem instantiateFieldsAt_parallel (depth : Nat) (replacement : Term Head) (fields : Fields Head) :
    Term.Fields.instantiateAt depth replacement fields =
      substituteFields (singleEnvironment depth replacement) fields := by
  cases fields with
  | nil => rfl
  | cons binders body rest =>
    rw [Term.Fields.instantiateAt, substitute_fields_cons, singleEnvironment_under,
      instantiateAt_parallel, instantiateFieldsAt_parallel]
end

theorem prefix_singleton (remaining : Nat) (argument body : Term Head) :
    applyPrefix (remaining + 1) [argument] body =
      Term.instantiateAt 0 (Term.lift 0 remaining argument) body := by
  rw [instantiateAt_parallel]
  unfold applyPrefix
  congr 1
  funext i
  cases i with
  | zero =>
    simp [prefixEnvironment, argumentAt, singleEnvironment, Term.instantiateAt,
      lift_zero_eq_renameMany, show (fun i : Nat => i) = id from rfl]
  | succ i =>
    by_cases before : i + 1 < remaining + 1
    · simp [prefixEnvironment, singleEnvironment, Term.instantiateAt, before]
    · simp [prefixEnvironment, singleEnvironment, Term.instantiateAt, before]
      omega

/-- The recursive equation used by the reference-only implementation. -/
theorem applyPrefix_cons (argument : Term Head) (arguments : List (Term Head)) (body : Term Head) :
    applyPrefix arguments.length arguments
        (Term.instantiateAt 0 (Term.lift 0 arguments.length argument) body) =
      applyPrefix (arguments.length + 1) (argument :: arguments) body := by
  rw [← prefix_singleton]
  simpa using applyPrefix_append (arguments.length + 1) [argument] arguments
    (by simp only [List.length_singleton]; omega) body

theorem applyPrefix_cons_of_le (arity : Nat) (argument : Term Head)
    (arguments : List (Term Head)) (body : Term Head) (count : arguments.length + 1 ≤ arity) :
    applyPrefix (arity - 1) arguments
        (Term.instantiateAt 0 (Term.lift 0 (arity - 1) argument) body) =
      applyPrefix arity (argument :: arguments) body := by
  have positive : arity - 1 + 1 = arity := by omega
  rw [← prefix_singleton, positive]
  simpa using applyPrefix_append arity [argument] arguments
    (by simp only [List.length_singleton]; omega) body

/-- Full prefix application agrees with the scoped simultaneous graft. -/
theorem applyPrefix_full {arity : Nat} (arguments : List (Term Head)) (body : Term Head)
    (count : arguments.length = arity) (supported : Term.supportedAt arity body = true) :
    graft arity arguments body = some (applyPrefix arity arguments body) := by
  simp only [graft, count, supported, and_self, ↓reduceIte]
  congr 1
  apply Term.substituteMany_congr_scoped _ body supported
  intro i inside
  simp [prefixEnvironment, count, inside, show (fun i : Nat => i) = id from rfl]

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.GraftSemantics
