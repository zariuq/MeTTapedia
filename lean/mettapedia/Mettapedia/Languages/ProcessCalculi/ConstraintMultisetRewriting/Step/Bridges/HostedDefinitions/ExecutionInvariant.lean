import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.MainReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.SearchReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PlugReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RootReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramRuns

/-!
# Successful-trace interpretation of the actual compiled definition program

The invariant retains a native directed prefix and the literal controller's
typed context. Helper histories and source reductions are proof evidence, not
admission conditions or runtime fields. The native prefix advances precisely
when an actual primitive or generated root clause is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionInvariant

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextStack

def nextContinuation : MClosed := nodeC "hd-main-eval-next" [finishContinuation]
def plugContinuation {n : Nat} (stack : Stack 0 n) : MClosed :=
  nodeC "hd-main-plug" [code stack, nextContinuation]

abbrev Reaches {dev : Definitions.Development} (built : Compiled dev) (first last : Tower.Tm 0) : Prop :=
  StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) first last

inductive Represents {dev : Definitions.Development} (built : Compiled dev) (initial : Tower.Tm 0) : MClosed → Prop
  | evaluating (term : Tower.Tm 0) (reached : Reaches built initial term) :
      Represents built initial (evaluateC (encodeTm term) finishContinuation)
  | searching (term : Tower.Tm 0) (reached : Reaches built initial term) {current : MClosed}
      (search : SearchReadback.Seeking term nextContinuation current) : Represents built initial current
  | rooted (term : Tower.Tm 0) (reached : Reaches built initial term) {current : MClosed}
      (root : SearchReadback.Rooted term nextContinuation current) : Represents built initial current
  | pending {n : Nat} (result : Tower.Tm n) (stack : Stack 0 n)
      (reached : Reaches built initial (plug stack result)) {current : MClosed}
      (helper : HelperPending.Pending result (plugContinuation stack) current) : Represents built initial current
  | resumingPlug {n : Nat} (result : Tower.Tm n) (stack : Stack 0 n)
      (reached : Reaches built initial (plug stack result)) :
      Represents built initial (resumeC (encodeTm result) (plugContinuation stack))
  | plugging (term : Tower.Tm 0) (reached : Reaches built initial term) {current : MClosed}
      (reconstruct : PlugReadback.Plugging term nextContinuation current) : Represents built initial current
  | resuming (term : Tower.Tm 0) (reached : Reaches built initial term) :
      Represents built initial (resumeC (encodeTm term) nextContinuation)
  | checking (term : Tower.Tm 0) (reached : Reaches built initial term) {current : MClosed}
      (worker : ValueWorker.Invariant (encodeTm term) current) : Represents built initial current
  | finished (term : Tower.Tm 0) (reached : Reaches built initial term) (value : DirectedAnswers.Value term) :
      Represents built initial (doneC (encodeTm term))

theorem initial {dev : Definitions.Development} (built : Compiled dev) (term : Tower.Tm 0) :
    Represents built term (queryCode term) := .evaluating term .refl

theorem step {dev : Definitions.Development} (built : Compiled dev) {initial : Tower.Tm 0}
    {before after : MClosed} (represented : Represents built initial before)
    (moved : ProgramBinders.Rewrites built.rules.get before after) : Represents built initial after := by
  cases represented with
  | evaluating term reached =>
      rcases MainReadback.eval_step built _ _ _ moved with rfl | rfl
      · exact .checking term reached (ValueWorker.initialized _)
      · exact .searching term reached (SearchReadback.initial term nextContinuation)
  | searching term reached search =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := search
      have classified := MainReadback.seek_step built _ _ _ _ moved
      rcases SearchReadback.cases_preserve ⟨n, focus, stack, rfl, restored⟩ classified with seeking | rooted
      · exact .searching term reached seeking
      · exact .rooted term reached rooted
  | rooted term reached root =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := root
      obtain ⟨output, reduced, pendingOrResume⟩ := RootReadback.of_step built focus _ _ moved
      have wholeStep : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows)
          term (plug stack output) := by
        rw [← restored]
        exact (context stack).step (rules := DirectedSyntax.directedRules (Definitions.devPackage dev built.nativeRows)) reduced
      have nextReached := reached.tail wholeStep
      rcases pendingOrResume with pending | rfl
      · exact .pending output stack nextReached pending
      · exact .resumingPlug output stack nextReached
  | pending result stack reached helper =>
      rcases HelperPending.advance built helper moved with pending | rfl
      · exact .pending result stack reached pending
      · exact .resumingPlug result stack reached
  | resumingPlug result stack reached =>
      have same := MainReadback.resume_plug_step built (encodeTm result) (code stack) nextContinuation _ moved
      subst after
      exact .plugging (plug stack result) reached ⟨_, result, stack, rfl, rfl⟩
  | plugging term reached reconstruct =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := reconstruct
      have classified := MainReadback.plug_step built _ _ _ _ moved
      rcases PlugReadback.cases_preserve ⟨n, focus, stack, rfl, restored⟩ classified with plugging | returned
      · exact .plugging term reached plugging
      · exact returned.symm ▸ Represents.resuming term reached
  | resuming term reached =>
      have same := MainReadback.resume_eval_step built (encodeTm term) finishContinuation _ moved
      subst after
      exact .evaluating term reached
  | checking term reached worker =>
      rcases ValueWorker.program_step_preserves built worker moved with kept | finished
      · exact .checking term reached kept
      · obtain ⟨value, isValue, same, rfl⟩ := finished
        have sameTerm : term = value := encodeTm_injective same
        subst term
        exact .finished value reached isValue
  | finished term reached value =>
      exact False.elim (ValueWorker.no_step_at_done built (encodeTm term) after moved)

theorem runs {dev : Definitions.Development} (built : Compiled dev) {initial : Tower.Tm 0}
    {before after : MClosed} (represented : Represents built initial before)
    (run : RuleInstances.Steps built.rules before after) : Represents built initial after := by
  induction run with
  | refl => exact represented
  | tail _ moved ih => exact step built ih moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionInvariant
