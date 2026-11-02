import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases

/-!
# Executable selection retains a typed solver case and its queue location

The recognizers use the common equality and variable-spine operations.
Identical terms discharge directly. Same-hole pruning retains an explicit
inequality of its parameter maps; different holes retain their sort witness.
Unimplemented cases leave the actual equation in the queue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelect

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

private def extendedOperators (sort : S.Srt) : DecidableEq ((signature S source).Op sort) :=
  inferInstanceAs (DecidableEq (S.Op sort ⊕ Operator source sort))

def tryReflexiveTerms {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    Option (RootCase S source (observe left, observe right)) := by
  letI := extendedOperators (S := S) (source := source)
  by_cases same : left = right
  · subst right
    exact some (.reflexive left)
  · exact none

def trySameTerms : {Γ : Ctx S} → {sort : S.Srt} →
    (left right : Term (signature S source) Γ sort) → Option (RootCase S source (observe left, observe right))
  | _, _, .var _, _ => none
  | _, _, .op (.inl _) _, _ => none
  | _, _, .op (.inr (.mk _)) _, .var _ => none
  | _, _, .op (.inr (.mk _)) _, .op (.inl _) _ => none
  | _, _, .op (.inr (.mk identity)) arguments, .op (.inr otherKey) remaining => by
      by_cases same : otherKey.key = identity
      · have keys : otherKey = Operator.mk identity := Operator.key_injective (S := S) same
        subst otherKey
        letI := extendedOperators (S := S) (source := source)
        by_cases identical : arguments = remaining
        · subst remaining
          exact some (.reflexive (.op (.inr (.mk identity)) arguments))
        · exact match first : VariableSpines.recognize (S := signature S source) (source identity).1 arguments with
          | none => none
          | some rho => by
              exact match second : VariableSpines.recognize (S := signature S source) (source identity).1 remaining with
              | none => none
              | some sigma => by
                  have different : rho ≠ sigma := by
                    intro equal
                    have terms : Term.op (S := signature S source) (.inr (.mk identity)) arguments =
                        Term.op (S := signature S source) (.inr (.mk identity)) remaining := by
                      rw [VariableSpines.application_eq_rename_generator identity arguments rho
                        (VariableSpines.sound _ arguments rho first),
                        VariableSpines.application_eq_rename_generator identity remaining sigma
                        (VariableSpines.sound _ remaining sigma second), equal]
                    exact identical (eq_of_heq (Term.op.inj terms).2)
                  refine some ?_
                  rw [VariableSpines.application_eq_rename_generator identity arguments rho
                    (VariableSpines.sound _ arguments rho first),
                    VariableSpines.application_eq_rename_generator identity remaining sigma
                    (VariableSpines.sound _ remaining sigma second)]
                  exact RootCase.selfPair (S := S) (source := source) identity rho sigma different
      · exact none

def tryRigidTerms : {Γ : Ctx S} → {sort : S.Srt} →
    (left right : Term (signature S source) Γ sort) → Option (RootCase S source (observe left, observe right))
  | _, _, .op (.inr (.mk identity)) arguments, .op (.inl operator) fields =>
      match computed : VariableSpines.recognize (S := signature S source) (source identity).1 arguments with
      | none => none
      | some rho => some (by
          rw [VariableSpines.application_eq_rename_generator identity arguments rho
            (VariableSpines.sound _ arguments rho computed)]
          exact RootCase.imitation (S := S) (source := source) identity rho operator fields)
  | _, _, _, _ => none

def tryFreshTerms {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    Option (RootCase S source (observe left, observe right)) :=
  (trySameTerms left right).orElse fun _ =>
    (tryRigidTerms left right).orElse fun _ => (tryRigidTerms right left).map fun selected => .reverse selected

def tryFlexEquation : (equation : Equation (Observation S source)) → Option (RootCase S source equation)
  | (⟨Γ, _, .op (.inr (.mk first)) left⟩, ⟨Δ, _, .op (.inr (.mk second)) right⟩) => by
      by_cases different : first ≠ second
      · by_cases contexts : Γ = Δ
        · subst Δ
          by_cases sorts : (source first).2 = (source second).2
          · exact match firstSpine : VariableSpines.recognize (S := signature S source) (source first).1 left with
            | none => none
            | some rho => by
                exact match secondSpine : VariableSpines.recognize (S := signature S source) (source second).1 right with
                | none => none
                | some sigma => by
                    refine some ?_
                    rw [VariableSpines.application_eq_rename_generator first left rho
                      (VariableSpines.sound _ left rho firstSpine),
                      VariableSpines.application_eq_rename_generator second right sigma
                      (VariableSpines.sound _ right sigma secondSpine)]
                    exact .flexPair first second different sorts rho sigma
          · exact none
        · exact none
      · exact none
  | _ => none

def tryTerms {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    Option (RootCase S source (observe left, observe right)) :=
  (tryReflexiveTerms left right).orElse fun _ =>
    ((ContextualBindingCase.tryTerms left right).map RootCase.binding).orElse fun _ =>
      (tryFlexEquation (observe left, observe right)).orElse fun _ => tryFreshTerms left right

def tryEquation (equation : Equation (Observation S source)) : Option (RootCase S source equation) := by
  rcases equation with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  exact if contexts : Γ = Δ then by
    subst Δ
    exact if sorts : sort = result then by
      subst result
      exact tryTerms left right
    else none
  else none

def choose : (problem : Problem source) → Option (Choice problem)
  | [] => none
  | equation :: rest =>
      match tryEquation equation with
      | some selected => some ⟨[], equation, selected, rest, rfl⟩
      | none => (choose rest).map fun selected => selected.prepend equation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelect
