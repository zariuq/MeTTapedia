import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingCompiled
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RootReadback

/-!
# Actual pattern probes detect the compiled program's root computations

The probe list is selected from literal paths in the actual finite rule list.
Its admission is the source language's constraint solvability, with its real
fresh copies. Grounded calls reflect to actual binder-equation answers; the
converse extends an existing solution at a fresh scope. A directed root action
therefore enables a probe, and a directed normal form enables none.

These are admission laws, not yet a theorem about completed scanner runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev)

def Selected (call : MClosed) : Prop :=
  ∃ index ∈ NormalProgram.rootIndices built, ∃ answer,
    ProgramBinders.Answers (built.rules.get index) call answer

def Enabled (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) : Prop :=
  ∃ clause ∈ NormalProgram.probes built D,
    Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
      NormalProbe.wrap call)])

theorem selected_of_enabled (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) (call : MClosed)
    (determined : Determines K term call) (enabled : Enabled built D scope K term) :
    Selected built call := by
  obtain ⟨clause, member, live⟩ := enabled
  obtain ⟨index, selected, rfl⟩ := List.mem_map.mp member
  have unwrapped := (NormalProbe.copied_match_iff
    (BinderCore.embedEquation built.rules index) scope K term).mp live
  simp only [BinderCore.embedEquation, BinderCore.copy_embed] at unwrapped
  obtain ⟨answer, answered, _⟩ := GroundCall.selected_determines built.rules index scope K term call
    determined (NormalGroundingCompiled.grounded built _ (List.get_mem built.rules index)) unwrapped
  exact ⟨index, selected, answer, answered⟩

theorem enabled_of_selected (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) (call : MClosed)
    (fresh : BinderCore.Fresh built.rules scope K term)
    (read : Reads K term call) (selected : Selected built call) :
    Enabled built D scope K term := by
  obtain ⟨index, inside, answer, answered⟩ := selected
  have output := BinderCore.reads_forward built.rules fresh read index answered
  have live : Solvable (K ++ [(instantiate (BinderCore.stamp built.rules scope index)
      (built.rules.get index).lhs, term)]) := by
    obtain ⟨X, family, assignment, solved, _⟩ := output
    exact ⟨X, family, assignment, solved⟩
  refine ⟨NormalProbe.equation (BinderCore.embedEquation built.rules index),
    List.mem_map.mpr ⟨index, inside, rfl⟩, ?_⟩
  apply (NormalProbe.copied_match_iff (BinderCore.embedEquation built.rules index) scope K term).mpr
  simpa only [BinderCore.embedEquation, BinderCore.copy_embed] using live

theorem enabled_iff (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) (call : MClosed)
    (fresh : BinderCore.Fresh built.rules scope K term) (determined : Determines K term call) :
    Enabled built D scope K term ↔ Selected built call :=
  ⟨selected_of_enabled built D scope K term call determined,
    enabled_of_selected built D scope K term call fresh ((determined.reads_iff call).mpr rfl)⟩

theorem rule_has_phase (index : Fin built.rules.length) :
    ∃ phase, LiteralPaths.symbolAt (built.rules.get index).lhs [1, 0] = some phase := by
  have member := List.get_mem built.rules index
  change built.rules.get index ∈ (ContextRules.fixed ++ RuntimeSubstitution.rules) ++ built.authored at member
  rcases List.mem_append.mp member with fixedOrHelper | authored
  · rcases List.mem_append.mp fixedOrHelper with fixed | helper
    · obtain ⟨phase, _, named⟩ := RowPhases.fixed_phase fixed
      exact ⟨phase, named⟩
    · have checked : RuntimeSubstitution.rules.all
          (fun rule => (LiteralPaths.symbolAt rule.lhs [1, 0]).isSome) = true := by decide +kernel
      have yes := List.all_eq_true.mp checked _ helper
      cases named : LiteralPaths.symbolAt (built.rules.get index).lhs [1, 0] with
      | none => rw [named] at yes; cases yes
      | some phase => exact ⟨phase, rfl⟩
  · exact ⟨"hd-root", RowPhases.authored_phase built authored⟩

theorem root_answer_selected {n : Nat} (term : Tower.Tm n) (continuation answer : MClosed)
    (index : Fin built.rules.length)
    (answered : ProgramBinders.Answers (built.rules.get index) (rootC (encodeTm term) continuation) answer) :
    index ∈ NormalProgram.rootIndices built := by
  obtain ⟨phase, named⟩ := rule_has_phase built index
  have observed := answered_phase named answered
  change some "hd-root" = some phase at observed
  have same : "hd-root" = phase := Option.some.inj observed
  exact (NormalProgram.root_indices_exact built index).mpr (same ▸ named)

theorem selected_of_root_step {n : Nat} (term : Tower.Tm n) (continuation answer : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (rootC (encodeTm term) continuation) answer) :
    Selected built (rootC (encodeTm term) continuation) := by
  obtain ⟨index, answered⟩ := step
  exact ⟨index, root_answer_selected built term continuation answer index answered, answer, answered⟩

theorem action_selected {n : Nat} (action : ComputationSyntax.Action (RootRewrites.presentation built) n)
    (allowed : DirectedSyntax.allowed action = true) (continuation : MClosed) :
    Selected built (rootC (encodeTm action.source) continuation) := by
  have executed := RootRewrites.action built action allowed continuation
  rcases executed.cases_head with same | ⟨next, first, _⟩
  · have phases := congrArg RuntimeSubstitution.phaseOf same
    change some "hd-root" = some "hd-resume" at phases
    exact False.elim ((by decide : ("hd-root" : String) ≠ "hd-resume") (Option.some.inj phases))
  · exact selected_of_root_step built action.source continuation next first

def Redex {n : Nat} (term : Tower.Tm n) : Prop :=
  ∃ action : ComputationSyntax.Action (RootRewrites.presentation built) n,
    DirectedSyntax.allowed action = true ∧ action.source = term

theorem primitive_redex {n : Nat} (term : Tower.Tm n) (continuation answer : MClosed)
    (step : PrimitiveCases.Case (rootC (encodeTm term) continuation) answer) : Redex built term := by
  generalize same : rootC (encodeTm term) continuation = current at step
  cases step with
  | beta body argument k =>
      obtain ⟨encoded, rfl⟩ := (RootReadback.root_eq _ _ _ _).mp same
      obtain ⟨function, argument, rfl, functionCode, rfl⟩ := PatternReadback.encoded_app encoded.symm
      obtain ⟨body, rfl, rfl⟩ := TermViews.lam_of_code functionCode
      exact ⟨.beta body argument, rfl, rfl⟩
  | first left right k =>
      obtain ⟨encoded, rfl⟩ := (RootReadback.root_eq _ _ _ _).mp same
      obtain ⟨subject, rfl, subjectCode⟩ := TermViews.fst_of_code encoded.symm
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code subjectCode
      exact ⟨.first left right, rfl, rfl⟩
  | second left right k =>
      obtain ⟨encoded, rfl⟩ := (RootReadback.root_eq _ _ _ _).mp same
      obtain ⟨subject, rfl, subjectCode⟩ := TermViews.snd_of_code encoded.symm
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code subjectCode
      exact ⟨.second left right, rfl, rfl⟩

theorem root_step_redex {n : Nat} (term : Tower.Tm n) (continuation answer : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (rootC (encodeTm term) continuation) answer) :
    Redex built term := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-root") rfl (by decide) step
  cases classification with
  | primitive edge => exact primitive_redex built term continuation answer edge
  | authored entry selected rule compiled answered =>
      obtain ⟨substitution, starts, _⟩ :=
        RowReadback.compiled_row_reflects entry compiled term continuation answer answered
      exact ⟨.declared entry.2.1 entry.2.2 selected substitution, rfl, starts⟩
  | traversal edge =>
      generalize same : rootC (encodeTm term) continuation = current at edge
      cases edge <;> simp [rootC, seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : rootC (encodeTm term) continuation = current at edge
      cases edge <;> simp [rootC, evaluateC, valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same

theorem selected_iff_redex {n : Nat} (term : Tower.Tm n) (continuation : MClosed) :
    Selected built (rootC (encodeTm term) continuation) ↔ Redex built term := by
  constructor
  · rintro ⟨index, _, answer, answered⟩
    exact root_step_redex built term continuation answer ⟨index, answered⟩
  · rintro ⟨action, allowed, starts⟩
    rw [← starts]
    exact action_selected built action allowed continuation

theorem probe_iff_redex (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) {n : Nat} (term : Tower.Tm n)
    (continuation : MClosed)
    (fresh : BinderCore.Fresh built.rules scope K datum)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    Enabled built D scope K datum ↔ Redex built term :=
  (enabled_iff built D scope K datum _ fresh determined).trans (selected_iff_redex built term continuation)

theorem selected_reduces {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (selected : Selected built (rootC (encodeTm term) continuation)) :
    ∃ output : Tower.Tm n, StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) term output := by
  obtain ⟨index, _, answer, answered⟩ := selected
  obtain ⟨output, reduced, _⟩ := RootReadback.of_step built term continuation answer ⟨index, answered⟩
  exact ⟨output, reduced⟩

theorem normal_disables_selected {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (normal : ContextualDependentExecutableJoin.Normal (Definitions.devPackage dev built.nativeRows) term) :
    ¬ Selected built (rootC (encodeTm term) continuation) := by
  intro selected
  obtain ⟨output, reduced⟩ := selected_reduces built term continuation selected
  exact normal output reduced

theorem normal_disables_probes (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) {n : Nat} (term : Tower.Tm n)
    (continuation : MClosed)
    (determined : Determines K datum (rootC (encodeTm term) continuation))
    (normal : ContextualDependentExecutableJoin.Normal (Definitions.devPackage dev built.nativeRows) term) :
    ¬ Enabled built D scope K datum := by
  intro enabled
  exact normal_disables_selected built term continuation normal
    (selected_of_enabled built D scope K datum _ determined enabled)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching.enabled_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching.action_selected
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching.probe_iff_redex
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalRootMatching.normal_disables_probes
