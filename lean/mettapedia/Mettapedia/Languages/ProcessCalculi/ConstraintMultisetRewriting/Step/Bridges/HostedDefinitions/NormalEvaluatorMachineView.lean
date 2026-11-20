import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionInvariant
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgram

/-!
# One directed-reduction episode with the normal-profile continuation

The original context and substitution clauses retain their actual syntax.
The episode stops at the new normal-next continuation. Its source native
term stays fixed, and every successful return carries one genuine directed
step. Global evaluator prefixes are composed outside this local episode.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorMachineView

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextStack

def nextContinuation : MClosed := nodeC NormalProgram.nextTag []

def plugContinuation {n : Nat} (stack : ContextStack.Stack 0 n) : MClosed :=
  nodeC "hd-main-plug" [code stack, nextContinuation]

inductive Episode {dev : Definitions.Development} (built : Compiled dev) (before : Tower.Tm 0) : MClosed → Prop
  | searching {current : MClosed} (search : SearchReadback.Seeking before nextContinuation current) :
      Episode built before current
  | rooted {current : MClosed} (root : SearchReadback.Rooted before nextContinuation current) :
      Episode built before current
  | pending {n : Nat} (result : Tower.Tm n) (stack : ContextStack.Stack 0 n)
      (reduced : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before (plug stack result))
      {current : MClosed} (helper : HelperPending.Pending result (plugContinuation stack) current) :
      Episode built before current
  | resumingPlug {n : Nat} (result : Tower.Tm n) (stack : ContextStack.Stack 0 n)
      (reduced : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before (plug stack result)) :
      Episode built before (resumeC (encodeTm result) (plugContinuation stack))
  | plugging (after : Tower.Tm 0)
      (reduced : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after)
      {current : MClosed} (reconstruct : PlugReadback.Plugging after nextContinuation current) :
      Episode built before current
  | resuming (after : Tower.Tm 0)
      (reduced : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after) :
      Episode built before (resumeC (encodeTm after) nextContinuation)

theorem initial {dev : Definitions.Development} (built : Compiled dev) (before : Tower.Tm 0) :
    Episode built before (seekC (encodeTm before) emptyContext nextContinuation) :=
  .searching (SearchReadback.initial before nextContinuation)

theorem no_original_return_step {dev : Definitions.Development} (built : Compiled dev)
    (term after : MClosed) :
    ¬ ProgramBinders.Rewrites built.rules.get (resumeC term nextContinuation) after := by
  intro moved
  have classification := ProgramCases.at_main_phase built (phase := "hd-resume") rfl (by decide) moved
  cases classification with
  | traversal edge =>
      generalize same : resumeC term nextContinuation = current at edge
      cases edge <;> simp [seekC, plugC, resumeC, activeC, nextContinuation, NormalProgram.nextTag,
        DataEmbedding.nodeC_eq_iff] at same
  | primitive edge =>
      generalize same : resumeC term nextContinuation = current at edge
      cases edge <;> simp [rootC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : resumeC term nextContinuation = current at edge
      cases edge <;> simp [evaluateC, valueC, resumeC, finishContinuation, activeC, nextContinuation,
        NormalProgram.nextTag, DataEmbedding.nodeC_eq_iff] at same
  | authored entry selected rule compiled answered =>
      have impossible := MainReadback.authored_at_root compiled answered
      change some "hd-resume" = some "hd-root" at impossible
      simp at impossible

theorem step {dev : Definitions.Development} (built : Compiled dev) {before : Tower.Tm 0}
    {current after : MClosed} (known : Episode built before current)
    (moved : ProgramBinders.Rewrites built.rules.get current after) : Episode built before after := by
  cases known with
  | searching search =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := search
      have classified := MainReadback.seek_step built _ _ _ _ moved
      rcases SearchReadback.cases_preserve ⟨n, focus, stack, rfl, restored⟩ classified with seeking | rooted
      · exact .searching seeking
      · exact .rooted rooted
  | rooted root =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := root
      obtain ⟨output, reduced, pendingOrResume⟩ := RootReadback.of_step built focus _ _ moved
      have wholeStep : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows)
          before (plug stack output) := by
        rw [← restored]
        exact (context stack).step
          (rules := DirectedSyntax.directedRules (Definitions.devPackage dev built.nativeRows)) reduced
      rcases pendingOrResume with pending | rfl
      · exact .pending output stack wholeStep pending
      · exact .resumingPlug output stack wholeStep
  | pending result stack reduced helper =>
      rcases HelperPending.advance built helper moved with pending | rfl
      · exact .pending result stack reduced pending
      · exact .resumingPlug result stack reduced
  | resumingPlug result stack reduced =>
      have same := MainReadback.resume_plug_step built (encodeTm result) (code stack) nextContinuation _ moved
      subst after
      exact .plugging (plug stack result) reduced ⟨_, result, stack, rfl, rfl⟩
  | plugging term reduced reconstruct =>
      obtain ⟨n, focus, stack, rfl, restored⟩ := reconstruct
      have classified := MainReadback.plug_step built _ _ _ _ moved
      rcases PlugReadback.cases_preserve ⟨n, focus, stack, rfl, restored⟩ classified with plugging | returned
      · exact .plugging term reduced plugging
      · exact returned.symm ▸ Episode.resuming term reduced
  | resuming term _ => exact False.elim (no_original_return_step built _ _ moved)

theorem head {dev : Definitions.Development} (built : Compiled dev) {before : Tower.Tm 0}
    {current : MClosed} (known : Episode built before current) : closedHead current = some activeTag := by
  cases known with
  | searching search => obtain ⟨_, _, _, rfl, _⟩ := search; rfl
  | rooted root => obtain ⟨_, _, _, rfl, _⟩ := root; rfl
  | pending _ _ _ helper => exact HelperPending.head helper
  | resumingPlug => rfl
  | plugging _ _ reconstruct => obtain ⟨_, _, _, rfl, _⟩ := reconstruct; rfl
  | resuming => rfl

theorem resume_view {dev : Definitions.Development} (built : Compiled dev) {before : Tower.Tm 0}
    {current payload : MClosed} (known : Episode built before current)
    (same : current = resumeC payload nextContinuation) :
    ∃ after : Tower.Tm 0,
      StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after ∧
      payload = encodeTm after := by
  cases known with
  | searching search =>
      obtain ⟨_, _, _, rfl, _⟩ := search
      simp [seekC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | rooted root =>
      obtain ⟨_, _, _, rfl, _⟩ := root
      simp [rootC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | pending result stack reduced helper =>
      obtain ⟨phase, observed, inside⟩ := helper.1
      rw [same] at observed
      change some "hd-resume" = some phase at observed
      have member : phase ∈ RowPhases.mainPhases := by
        rw [← Option.some.inj observed]
        decide +kernel
      exact False.elim (HelperIsolation.phase_palettes_disjoint inside member)
  | resumingPlug result stack reduced =>
      simp [resumeC, activeC, plugContinuation, nextContinuation, NormalProgram.nextTag,
        DataEmbedding.nodeC_eq_iff] at same
  | plugging after reduced reconstruct =>
      obtain ⟨_, _, _, rfl, _⟩ := reconstruct
      simp [plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | resuming after reduced =>
      have parts : encodeTm after = payload ∧ nextContinuation = nextContinuation := by
        simpa [resumeC, activeC, DataEmbedding.nodeC_eq_iff] using same
      exact ⟨after, reduced, parts.1.symm⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorMachineView

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorMachineView.step
