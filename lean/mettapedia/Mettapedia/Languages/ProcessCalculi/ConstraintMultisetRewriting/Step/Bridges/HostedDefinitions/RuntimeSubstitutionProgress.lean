import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionDeterminism
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeZero
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeEnvironment

/-!
# Exact helper outcomes and absence of infinite internal execution

The finite helper has unique successors and no rule at the public resume port.
Its constructed runs therefore prove strong normalization of every initialized
helper call. Any other run reaching a resume port has the same value and the
same external continuation.

These statements concern the helper rule list. A containing program may
continue at the resume port; extension to its internal execution requires a
separate noninterference proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open LiteralPaths

def avoidsResume (equation : Equation) : Bool :=
  match symbolAt equation.lhs [1, 0] with
  | none => false
  | some phase => decide (phase ≠ "hd-resume")

theorem resume_boundary_checked : rules.all avoidsResume = true := by decide +kernel

theorem resume_symbol {X : Type} (target : X → MetaArity MSig) (value continuation : MClosed) :
    symbolAt (Rigid.includeTerm target (resumeC value continuation)) [1, 0] = some "hd-resume" := by
  rfl

theorem no_resume_step (value continuation : MClosed) : ¬ ∃ next, Step (resumeC value continuation) next := by
  rintro ⟨next, index, environment, matched, _⟩
  have checked := List.all_eq_true.mp resume_boundary_checked (rules.get index) (List.get_mem _ _)
  change avoidsResume (rules.get index) = true at checked
  unfold avoidsResume at checked
  cases located : symbolAt (rules.get index).lhs [1, 0] with
  | none =>
      rw [located] at checked
      cases checked
  | some phase =>
      rw [located] at checked
      have different : phase ≠ "hd-resume" := of_decide_eq_true checked
      have named := symbolAt_instantiate ((rules.get index).assign environment (ProgramBinders.ground MSig)) located
      rw [matched, resume_symbol] at named
      exact different (Option.some.inj named).symm

theorem normalizing_of_run {first last : MClosed} (run : Runs first last)
    (stopped : ¬ ∃ next, Step last next) : Acc (fun after before => Step before after) first := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact .intro _ (fun next step => False.elim (stopped ⟨next, step⟩))
  | @head before _middle edge _rest ih =>
      refine .intro before ?_
      intro next nextEdge
      have same := step_deterministic edge nextEdge
      subst next
      exact ih

theorem normal_endpoints_unique {start first second : MClosed}
    (one : Runs start first) (two : Runs start second)
    (firstStopped : ¬ ∃ next, Step first next) (secondStopped : ¬ ∃ next, Step second next) :
    first = second := by
  induction one using Relation.ReflTransGen.head_induction_on generalizing second with
  | refl =>
      rcases two.cases_head with same | ⟨next, step, _⟩
      · exact same
      · exact False.elim (firstStopped ⟨next, step⟩)
  | @head _before middle edge _rest ih =>
      rcases two.cases_head with same | ⟨next, nextEdge, later⟩
      · subst second
        exact False.elim (secondStopped ⟨middle, edge⟩)
      · have same := step_deterministic edge nextEdge
        subst next
        exact ih later secondStopped

theorem resume_endpoints {start first second firstContinuation secondContinuation : MClosed}
    (one : Runs start (resumeC first firstContinuation))
    (two : Runs start (resumeC second secondContinuation)) :
    first = second ∧ firstContinuation = secondContinuation := by
  have endpoints := normal_endpoints_unique one two (no_resume_step _ _) (no_resume_step _ _)
  simpa [resumeC, activeC, DataEmbedding.nodeC_eq_iff] using endpoints

theorem shift_normalizing (amount cutoff : Nat) (term : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Acc (fun after before => Step before after) (shiftC amount cutoff (quoteRaw term) continuation) :=
  normalizing_of_run (shift_runs amount cutoff term continuation) (no_resume_step _ _)

theorem zero_normalizing (replacement : NativeSyntax.Raw Tower.Head) (depth : Nat)
    (body : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Acc (fun after before => Step before after)
      (substituteZeroC (quoteRaw replacement) depth (quoteRaw body) continuation) :=
  normalizing_of_run (zero_runs replacement depth body continuation) (no_resume_step _ _)

theorem environment_normalizing (environment : List (NativeSyntax.Raw Tower.Head))
    (body : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Acc (fun after before => Step before after)
      (substituteEnvironmentC (encodeRawEnv environment) (quoteRaw body) continuation) :=
  normalizing_of_run (environment_runs environment body continuation) (no_resume_step _ _)

theorem shift_reflects (amount cutoff : Nat) (term : NativeSyntax.Raw Tower.Head) (continuation value after : MClosed)
    (run : Runs (shiftC amount cutoff (quoteRaw term) continuation) (resumeC value after)) :
    value = quoteRaw (NativeSyntax.shift amount cutoff term) ∧ after = continuation :=
  resume_endpoints run (shift_runs amount cutoff term continuation)

theorem zero_reflects (replacement : NativeSyntax.Raw Tower.Head) (depth : Nat)
    (body : NativeSyntax.Raw Tower.Head) (continuation value after : MClosed)
    (run : Runs (substituteZeroC (quoteRaw replacement) depth (quoteRaw body) continuation) (resumeC value after)) :
    value = quoteRaw (NativeSyntax.substituteZero replacement depth body) ∧ after = continuation :=
  resume_endpoints run (zero_runs replacement depth body continuation)

theorem environment_reflects (environment : List (NativeSyntax.Raw Tower.Head))
    (body : NativeSyntax.Raw Tower.Head) (continuation value after : MClosed)
    (run : Runs (substituteEnvironmentC (encodeRawEnv environment) (quoteRaw body) continuation) (resumeC value after)) :
    value = quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) body) ∧ after = continuation :=
  resume_endpoints run (environment_runs environment body continuation)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
