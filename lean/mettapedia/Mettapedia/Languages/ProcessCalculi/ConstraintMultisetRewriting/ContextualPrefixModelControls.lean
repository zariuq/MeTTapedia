import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPrincipals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

/-!
# Unused future scopes add names, not their later caller constraints

A prefix model extends even when its original closed term sort is empty.
Adding an unused higher-arity declaration does not equate two caller names;
a later tell can equate them only in the later equation problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModelControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

abbrev emptySignature : Signature where
  Srt := Unit
  Op _ := Empty
  arity operator := nomatch operator

abbrev noDeclarations : Empty → MetaArity emptySignature := fun name => nomatch name
abbrev newDeclaration (_ : Unit) : MetaArity emptySignature := ([], ())

def oldCandidate : Assignment noDeclarations noDeclarations := fun name => nomatch name

theorem no_old_closed_term (term : Term (signature emptySignature noDeclarations) [] ()) : False := by
  cases term with
  | var position => nomatch position
  | op head _arguments =>
      cases head with
      | inl head => nomatch head
      | inr head => exact Empty.elim head.key

theorem there_is_no_total_assignment_of_new_names_back_into_old_frame
    (candidate : Assignment (extended newDeclaration noDeclarations) noDeclarations) : False :=
  no_old_closed_term (candidate (.inl ()))

theorem empty_prefix_extends_without_an_old_ground_term :
    ContextualFrameUnifier.Models (ContextualStoredRows.liftCaptures newDeclaration oldCandidate)
      (ContextualFrameUnifier.mapProblem (inclusion newDeclaration noDeclarations)
        ([] : EquationStore (Term (signature emptySignature noDeclarations) [] ()))) := by
  apply (lifted_prefix_models_iff newDeclaration oldCandidate []).mpr
  intro equation member
  cases member

abbrev callers (_ : Bool) : MetaArity emptySignature := ([], ())
abbrev futureScope (_ : Unit) : MetaArity emptySignature := ([()], ())
abbrev wide := extended futureScope callers

def callerU : Term (signature emptySignature wide) [] () := generator wide (.inr false)
def callerV : Term (signature emptySignature wide) [] () := generator wide (.inr true)
def rows (_ : Nat) : ContextualStoredRows.Row noDeclarations wide [] () := .shared callerU

def aliasCallers : Assignment callers callers := fun _ => generator callers false
def oldCallerProblem : EquationStore (Term (signature emptySignature callers) [] ()) :=
  [(generator callers false, generator callers true)]

theorem alias_answer_is_principal : ContextualFrameUnifier.Principal oldCallerProblem aliasCallers := by
  refine ⟨?_, ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    rw [instantiate_generator, instantiate_generator]
    rfl
  · intro Future future candidate solved
    have equal := solved (generator callers false, generator callers true) (List.mem_singleton_self _)
    rw [instantiate_generator, instantiate_generator] at equal
    refine ⟨candidate, ?_⟩
    intro name
    change candidate name = instantiate candidate (generator callers false)
    rw [instantiate_generator]
    cases name
    · rfl
    · exact equal.symm

theorem real_caller_equation_and_unused_higher_arity_scope_are_kept :
    ContextualFrameUnifier.Principal
      (ContextualFrameUnifier.mapProblem (inclusion futureScope callers) oldCallerProblem)
      (ContextualStoredRows.liftCaptures futureScope aliasCallers) ∧
      ContextualStoredRows.liftCaptures futureScope aliasCallers (.inl ()) = generator wide (.inl ()) :=
  ⟨principal_with_unused futureScope alias_answer_is_principal, rfl⟩

theorem unused_scope_does_not_discharge_a_caller_equality :
    ¬ ContextualGuardSemantics.Ask noDeclarations [] rows ∅ (.equal callerU callerV) := by
  intro asked
  have equal := asked (Unit ⊕ Bool) wide (generator wide) (by intro equation member; cases member)
  change instantiate (generator wide) callerU = instantiate (generator wide) callerV at equal
  rw [instantiate_identity, instantiate_identity] at equal
  have heads := (Term.op.inj equal).1
  have names := congrArg Operator.key (Sum.inr.inj heads)
  cases names

theorem the_future_tell_has_its_own_later_ask :
    ContextualGuardSemantics.Ask noDeclarations [(callerU, callerV)] rows ∅ (.equal callerU callerV) :=
  ContextualGuardSemantics.Ask.equal_of_mem noDeclarations [(callerU, callerV)] rows ∅
    callerU callerV (List.mem_singleton_self _)

theorem later_constraints_cannot_be_imported_into_the_prefix_ask :
    ¬ ContextualGuardSemantics.Ask noDeclarations [] rows ∅ (.equal callerU callerV) ∧
      ContextualGuardSemantics.Ask noDeclarations [(callerU, callerV)] rows ∅ (.equal callerU callerV) :=
  ⟨unused_scope_does_not_discharge_a_caller_equality, the_future_tell_has_its_own_later_ask⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModelControls
