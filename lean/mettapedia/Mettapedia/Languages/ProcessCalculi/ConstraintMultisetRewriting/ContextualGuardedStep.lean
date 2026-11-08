import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors

/-!
# Activated occurrence firings retain their scoped guard asks

The equation and occurrence effects are the existing computed activation
effects. Every activated source check additionally asks over all later-family
models of that same equation store. Checks are not added as equations and
their variables remain part of the interface even for a closed output.

Consistency here is the ordinary action's consistency in the explicitly
chosen active frame. A runtime solver may first extend that frame with its
actual fresh helpers. No globally rich declaration carrier is required.

Execution uses the formation/resources/information admission. The original
fieldwise validity judgment remains its proved specification. The resource
component runs the occupation operator and retains source freshness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualGuardMatching
open ContextualActivatedStep

universe u
variable {S : Signature} {Local Shared Next : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def guardRows {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    O → ContextualStoredRows.Row locals (target locals captures) Γ sort :=
  fun occurrence => (rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures)

/-- Port, resource and guard obligations before equation solvability has
been established. Solver refutation operates on these obligations too. -/
structure Requirements [DecidableEq O] (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputLabel : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputLabel = (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.produce
  occurrences : Enabled outputLabel before.present (selection.commit (T := Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort))
  checks : ∀ check ∈ (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.checks,
    ContextualGuardSemantics.Ask locals (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
      (guardRows locals captures rows) before.present check

/-- Contextual admission permits solutions in any later declaration frame. -/
structure Valid [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputLabel : O → Term (signature S (target locals captures)) Γ sort)
    extends Requirements locals captures occupied selection rule rows before outputLabel where
  solvable : ContextualFrameUnifier.Solvable
    (problem locals captures occupied selection rule rows before)

theorem valid_iff_factors [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (target locals captures)) Γ sort) :
    Valid locals captures occupied selection rule rows before outputs ↔
      ContextualInteractionFactors.Admitted locals captures occupied selection rule rows before outputs := by
  constructor
  · intro valid
    exact ⟨⟨valid.take_length, valid.read_length, valid.outputs⟩,
      (ContextualInteractionFactors.resources_iff outputs selection before.present).mpr
        ⟨valid.take_distinct, valid.output_distinct, valid.occurrences⟩,
      ⟨valid.solvable, valid.checks⟩⟩
  · intro admitted
    obtain ⟨taken, made, enabled⟩ :=
      (ContextualInteractionFactors.resources_iff outputs selection before.present).mp admitted.resources
    exact ⟨⟨taken, made, admitted.formation.take_length, admitted.formation.read_length,
      admitted.formation.outputs, enabled, admitted.information.checks⟩, admitted.information.solvable⟩

def Step [DecidableEq O] (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (after : Configuration (Term (signature S (target locals captures)) Γ sort) O)
    (afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort)
    (afterOccupied : Finset Nat) : Prop :=
  ∃ selection, ContextualInteractionFactors.Admitted locals captures occupied selection rule rows before outputs ∧
    after = result locals captures occupied selection rule rows before ∧
      afterRows = resultRows locals captures selection outputs rows ∧
        afterOccupied = ContextualActivationScopes.after occupied selection

theorem valid_iff_positive [DecidableEq O] {occupied : Finset Nat} {selection : Selection O}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)} (noChecks : rule.checks = [])
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort} :
    Valid locals captures occupied selection rule rows before outputs ↔
      ContextualActivatedStep.Valid locals captures occupied selection rule rows before outputs := by
  constructor
  · intro valid
    exact ⟨noChecks, valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
      valid.outputs, valid.occurrences, valid.solvable⟩
  · intro valid
    refine ⟨⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
      valid.outputs, valid.occurrences, ?_⟩, valid.solvable⟩
    intro check member
    simp only [prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, noChecks, List.map_nil, List.not_mem_nil] at member

theorem step_iff_positive [DecidableEq O] {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)} (noChecks : rule.checks = [])
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat} :
    Step locals captures occupied rule rows before outputs after afterRows afterOccupied ↔
      ContextualActivatedStep.Step locals captures occupied rule rows before outputs after afterRows afterOccupied := by
  simp only [Step, ContextualActivatedStep.Step, ← valid_iff_factors,
    valid_iff_positive locals captures noChecks]

theorem Step.solvable [DecidableEq O] {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat}
    (step : Step locals captures occupied rule rows before outputs after afterRows afterOccupied) :
    ContextualFrameUnifier.Solvable after.equations := by
  obtain ⟨selection, valid, rfl, _, _⟩ := step
  exact valid.information.solvable

theorem Step.refines_old_frame [DecidableEq O] {Later : Type} (later : Later → MetaArity S)
    {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat}
    (step : Step locals captures occupied rule rows before outputs after afterRows afterOccupied)
    (candidate : Assignment (target locals captures) later)
    (solved : ContextualFrameUnifier.Models candidate after.equations) :
    ContextualFrameUnifier.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) before.equations := by
  obtain ⟨selection, _, rfl, _, _⟩ := step
  exact models_refine_old_frame locals captures later occupied selection rule rows before candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep
