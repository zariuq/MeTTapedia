import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Completeness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativePublic

/-!
# Compiled native reductions reach the actual public frontier

The chain uses the development's generated rows, the finite source program,
the real public query, and the existing native frontier. Its observation is
literal value membership in the frontier's bag of reading sets. It does not
identify the number of reduction strategies with answer multiplicity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativeExecution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev)
  (D : Discipline MSig [] ()) (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)

def program : SourceLanguage.Program (BinderCore.keys built.rules) [] () D.Ty :=
  BinderCore.program built.rules

def Answer (term value : Tower.Tm 0) : Prop :=
  ∃ next, (FrontierArrow.target (D := D) N (program built D)).MultiStep
    (FrontierArrow.initialState (D := D) N (program built D)
      (PublicQuery.query RuntimeSubstitution.rules built.authored (queryCode term))) next ∧
    NativePublic.Contains (FrontierArrow.answers N next) (encodeTm value)

include supply

theorem done_iff_answer (term value : Tower.Tm 0) :
    RuleInstances.Steps built.rules (queryCode term) (doneC (encodeTm value)) ↔
      Answer built D N term value :=
  NativePublic.public_answers_by_native RuntimeSubstitution.rules built.authored D N supply
    built.separated (queryCode term) (encodeTm value) (.inl (active_head _ _))

theorem directed_value_executes {term value : Tower.Tm 0}
    (steps : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) term value)
    (isValue : DirectedAnswers.Value value) : Answer built D N term value :=
  (done_iff_answer built D N supply term value).mp (Completeness.value_reached built steps isValue)

theorem public_source_executes {term value : Tower.Tm 0}
    (steps : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) term value)
    (isValue : DirectedAnswers.Value value) :
    ∃ configuration, Runs D (program built D) supply
      (Config.initial (fun _ => 0)
        (PublicQuery.query RuntimeSubstitution.rules built.authored (queryCode term))) configuration ∧
      HasAnswer (D := D) built.rules configuration (encodeTm value) :=
  (PublicAnswers.public_answers_iff RuntimeSubstitution.rules built.authored D supply built.separated
    (queryCode term) (encodeTm value) (.inl (active_head _ _))).mp
      (Completeness.value_reached built steps isValue)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativeExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativeExecution.directed_value_executes
