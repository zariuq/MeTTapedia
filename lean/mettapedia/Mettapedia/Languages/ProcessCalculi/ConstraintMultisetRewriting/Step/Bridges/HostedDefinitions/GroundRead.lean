import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.LiteralPaths
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# Ground outputs from checked dependencies on an actual matched input

A path to each right-side slot recovers that slot in every target family,
including families with unresolved names. This is stronger than equality of
closed readings. The certificate concerns zero-arity template holes and is a
sufficient, executable condition on actual source templates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundRead

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder LiteralPaths

def valuesAt {X : Type} (target : X → MetaArity MSig) {slots : Nat}
    (environment : Fin slots → MClosed) : Assignment (FoArity slots) target :=
  fun index => Rigid.includeTerm target (environment index)

theorem include_materialize_at {X : Type} (target : X → MetaArity MSig) {slots : Nat}
    (environment : Fin slots → MClosed) (template : Template slots) :
    Rigid.includeTerm target (materialize environment template) =
      instantiate (valuesAt target environment) template := by
  have included := congrArg (instantiate (ProgramBinders.fromGround target)) (include_materialize environment template)
  rw [Rigid.instantiate_include, ← Assignment.instantiate_compose] at included
  have assignment : Assignment.compose (ProgramBinders.fromGround target) (values environment) =
      valuesAt target environment := by
    funext index
    exact Rigid.instantiate_include (ProgramBinders.fromGround target) (environment index)
  rw [assignment] at included
  exact included

theorem recover_in_target {X : Type} {target : X → MetaArity MSig} {slots : Nat}
    (lhs : Template slots) (index : Fin slots) (path : List Nat)
    (located : part lhs path = some (slot index))
    (assignment : Assignment (FoArity slots) target) (environment : Fin slots → MClosed)
    (matched : instantiate assignment lhs = Rigid.includeTerm target (materialize environment lhs)) :
    assignment index = Rigid.includeTerm target (environment index) := by
  have instantiated := matched.trans (include_materialize_at target environment lhs)
  have parts := congrArg (fun term => part term path) instantiated
  rw [part_instantiate assignment located, part_instantiate (valuesAt target environment) located,
    instantiate_slot, instantiate_slot] at parts
  exact Option.some.inj parts

def rhsPathsChecked {slots : Nat} (lhs rhs : Template slots) : Bool :=
  (support rhs).all fun index => pathChecks lhs index (chosenPath lhs index)

theorem rhs_paths_sound {slots : Nat} {lhs rhs : Template slots}
    (checked : rhsPathsChecked lhs rhs = true) (index : Fin slots) (used : index ∈ support rhs) :
    part lhs (chosenPath lhs index) = some (slot index) :=
  pathChecks_sound (List.all_eq_true.mp checked index used)

theorem output_in_target {X : Type} {target : X → MetaArity MSig} {slots : Nat}
    (lhs rhs : Template slots) (checked : rhsPathsChecked lhs rhs = true)
    (assignment : Assignment (FoArity slots) target) (environment : Fin slots → MClosed)
    (matched : instantiate assignment lhs = Rigid.includeTerm target (materialize environment lhs)) :
    instantiate assignment rhs = Rigid.includeTerm target (materialize environment rhs) := by
  rw [include_materialize_at target environment rhs]
  apply instantiate_congr assignment (valuesAt target environment) rhs
  intro index used
  exact recover_in_target lhs index (chosenPath lhs index) (rhs_paths_sound checked index used)
    assignment environment matched

def Grounding (equation : ProgramBinders.Equation MSig [] ()) : Prop :=
  ∀ {X : Type} (target : X → MetaArity MSig) (assignment : Assignment equation.arity target)
    (environment : equation.Ground),
    instantiate assignment equation.lhs = instantiate (equation.assign environment target) equation.lhs →
      instantiate assignment equation.rhs = instantiate (equation.assign environment target) equation.rhs

theorem equation_grounding {slots : Nat} (lhs rhs : Template slots)
    (checked : rhsPathsChecked lhs rhs = true) : Grounding (equation lhs rhs) := by
  intro X target assignment environment matched
  change instantiate assignment lhs = instantiate (valuesAt target environment) lhs at matched
  change instantiate assignment rhs = instantiate (valuesAt target environment) rhs
  have matchedClosed := matched.trans (include_materialize_at target environment lhs).symm
  exact (output_in_target lhs rhs checked assignment environment matchedClosed).trans
    (include_materialize_at target environment rhs)

section Controls

def identityLhs : Template 1 := node "input" [slot 0]
def identityRhs : Template 1 := node "output" [slot 0]

theorem identity_checked : rhsPathsChecked identityLhs identityRhs = true := by decide +kernel

theorem identity_ground_output {X : Type} (target : X → MetaArity MSig)
    (assignment : Assignment (FoArity 1) target) (datum : MClosed)
    (matched : instantiate assignment identityLhs =
      Rigid.includeTerm target (materialize (fun _ => datum) identityLhs)) :
    instantiate assignment identityRhs =
      Rigid.includeTerm target (materialize (fun _ => datum) identityRhs) :=
  output_in_target identityLhs identityRhs identity_checked assignment (fun _ => datum) matched

theorem uncovered_not_checked :
    rhsPathsChecked (literal (n := 1) (csym "input")) (slot 0) = false := by decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundRead

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundRead.output_in_target
