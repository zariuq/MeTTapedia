import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Transitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq

/-!
# Rule programs and the existing first-order and dependent steps

The existing admission/result proofs supply actual operational arrows.
First-order embedding needs the label-keeping restriction; dependent
embedding needs the fresh-program-opening restriction. Both keep the state
and knowledge through the original representation maps. These are successor
comparisons, not bijections of rule or opening origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Rules

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open LogicOverTheStep.StepSpan FragmentsOfTheStep.TransitionMaps

universe uT uS uO

section FirstOrder

open RuleSyntax.OneFrame

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)
  {O : Type uO} [DecidableEq O] (label : O → T) (program : RuleSyntax.Program (Terms T))

theorem firstOrderComparison : FunctionalBisimulation (Succ (firstOrderOn A label program))
    (Succ (keeping (O := O) A program)) (embed label) where
  zig := fun {s t} stepped => (firstOrder_eq (A := A) (label := label) (P := program) s t).mp stepped
  zag := by
    intro s next stepped
    obtain ⟨t, rfl⟩ := keeping_closed (A := A) (label := label) (P := program) s stepped
    exact ⟨t, (firstOrder_eq (A := A) (label := label) (P := program) s t).mpr stepped, rfl⟩

def firstOrderCorrespondence : OperationalCorrespondence
    (Execution.theory (firstOrderOn A label program)) (Execution.theory (keeping (O := O) A program)) :=
  Transitions.functionalCorrespondence (firstOrderComparison A label program)

end FirstOrder

section Dependent

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual ContextualDependentEta
open RuleSyntax.Dependent

variable {Head L : Type} {rules : Rules Head} [UniverseLevel.LevelOrder L]
  (levels : LevelModel rules L) {O : Type} [DecidableEq O]
  (program : RuleSyntax.Program (Terms rules))

abbrev dependentProgram := dependentOn (O := O) levels program
abbrev syntaxProgram := (RuleSyntax.step (frames levels) O helperExtensions program).toStep

theorem dependentComparison : FunctionalBisimulation (Succ (dependentProgram (O := O) levels program))
    (Succ (syntaxProgram (O := O) levels program)) toState where
  zig := fun {s t} stepped => (dependent_eq (levels := levels) (P := program) s t).mp stepped
  zag := by
    intro s next stepped
    exact ⟨ofState next, (dependent_eq (levels := levels) (P := program) s (ofState next)).mpr stepped, rfl⟩

def dependentCorrespondence : OperationalCorrespondence
    (Execution.theory (dependentProgram (O := O) levels program))
      (Execution.theory (syntaxProgram (O := O) levels program)) :=
  Transitions.functionalCorrespondence (dependentComparison (O := O) levels program)

def dependentTranslation : OperationalTranslation
    (Execution.theory (dependentProgram (O := O) levels program))
      (Execution.theory (syntaxProgram (O := O) levels program)) :=
  Transitions.translation (dependentComparison (O := O) levels program)

theorem syntaxComparison : FunctionalBisimulation (Succ (syntaxProgram (O := O) levels program))
    (Succ (dependentProgram (O := O) levels program)) ofState where
  zig := fun {s t} stepped => (dependent_eq (levels := levels) (P := program) (ofState s) (ofState t)).mpr stepped
  zag := by
    intro s next stepped
    exact ⟨toState next, (dependent_eq (levels := levels) (P := program) (ofState s) next).mp stepped, rfl⟩

def syntaxTranslation : OperationalTranslation
    (Execution.theory (syntaxProgram (O := O) levels program))
      (Execution.theory (dependentProgram (O := O) levels program)) :=
  Transitions.translation (syntaxComparison (O := O) levels program)

def syntaxCorrespondence : OperationalCorrespondence
    (Execution.theory (syntaxProgram (O := O) levels program))
      (Execution.theory (dependentProgram (O := O) levels program)) :=
  Transitions.functionalCorrespondence (syntaxComparison (O := O) levels program)

theorem state_roundtrip (state : RuleSyntax.State (Terms rules) O) :
    (dependentTranslation (O := O) levels program).mapTerm
      ((syntaxTranslation (O := O) levels program).mapTerm state) = state := rfl

/-- Every actual run through freshly opened program rules has a syntax
program run at the mapped endpoint and with the same firing count. -/
theorem dependent_run {state : DependentFull.State rules O}
    (run : (dependentProgram levels program).Run state) :
    ∃ syntaxRun : (syntaxProgram levels program).Run (toState state),
      syntaxRun.last = toState run.last ∧ syntaxRun.word.length = run.word.length := by
  let path := (dependentTranslation levels program).mapRoute
    (Execution.toPath (dependentProgram levels program) run)
  obtain ⟨syntaxRun, endpoint, length⟩ := Execution.path_has_run (syntaxProgram levels program) path
  refine ⟨syntaxRun, endpoint, length.trans ?_⟩
  exact ((dependentTranslation levels program).mapRoute_length _).trans
    (Execution.toPath_length (dependentProgram levels program) run)

end Dependent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Rules

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Rules.firstOrderCorrespondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Rules.dependentCorrespondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Rules.dependent_run
