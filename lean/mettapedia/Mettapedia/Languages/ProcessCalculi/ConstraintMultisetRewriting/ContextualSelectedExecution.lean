import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationProducers
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Actual contextual firings with rigid selected row views

Input patterns are fixed binding terms of the original signature. A selected
row's template view must really be the corresponding rigid term. Both shared
rows and rigid stored schemas are permitted. Reads retain their port
multiplicity, including aliases. Outputs may contain private contextual
locals and shared captures. The complete reflexive joint problem remains in
the semantic store, and the source solver discharges it at fuel one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectedNormalization
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

structure Interaction (before : Endpoint locals O Γ sort) extends ContextualExecutionCommutation.Producer before where
  taken : List O
  read : List O
  take_distinct : taken.Nodup
  take_available : taken.toFinset ⊆ before.inventory.configuration.present
  read_available : read.toFinset ⊆ before.inventory.configuration.present
  take_read_apart : Disjoint taken.toFinset read.toFinset
  label : O → Term S Γ sort
  template : ∀ occurrence ∈ taken ++ read,
    ContextualStoredRows.asTemplate locals before.declarations (before.inventory.rows occurrence) =
      Rigid.includeTerm (ContextualSelectionViews.source locals before.declarations) (label occurrence)

namespace Interaction

variable {before : Endpoint locals O Γ sort}

def selection (interaction : Interaction before) : Selection O := ⟨interaction.taken, interaction.read, interaction.made⟩
def scope (_interaction : Interaction before) := ContextualActivationScopes.start before.occupied
def rule (interaction : Interaction before) :
    RuleInstance (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort) :=
  ⟨interaction.taken.map (Rigid.includeTerm _ ∘ interaction.label),
    interaction.read.map (Rigid.includeTerm _ ∘ interaction.label), [], [], interaction.made.map interaction.value⟩
def outputs (interaction : Interaction before) : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort :=
  fun occurrence => ContextualFreshening.termAt locals before.declarations interaction.scope (interaction.value occurrence)
def terms (interaction : Interaction before) (prior : List (Term S Γ sort)) :=
  prior ++ interaction.taken.map interaction.label ++ interaction.read.map interaction.label

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem physical (interaction : Interaction before) :
    Enabled (fun _ : O => ()) before.inventory.configuration.present (interaction.selection.commit (T := Unit)) :=
  ⟨interaction.take_available, interaction.read_available, interaction.take_read_apart, interaction.fresh,
    fun _ member => by cases member⟩

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem rule_covered (interaction : Interaction before) :
    RuleCovered (privateScopes before.scopes) before.occupied interaction.rule := by
  intro value member
  change value ∈ interaction.taken.map (Rigid.includeTerm _ ∘ interaction.label) ++
    interaction.read.map (Rigid.includeTerm _ ∘ interaction.label) ++ [] ++ [] ++
      interaction.made.map interaction.value at member
  simp only [List.append_nil, List.mem_append] at member
  rcases member with (taken | read) | produced
  · obtain ⟨occurrence, _selected, rfl⟩ := List.mem_map.mp taken
    exact included_covered _ _ _ _
  · obtain ⟨occurrence, _selected, rfl⟩ := List.mem_map.mp read
    exact included_covered _ _ _ _
  · obtain ⟨occurrence, selected, rfl⟩ := List.mem_map.mp produced
    exact interaction.covered occurrence selected

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem taken_view (interaction : Interaction before) (position : Fin interaction.taken.length) :
    (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows).taken position =
        Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) (interaction.label (interaction.taken.get position)) := by
  rw [ContextualActivatedStep.prepared_taken_view]
  dsimp only [selection]
  rw [ContextualStoredRows.viewAt_eq_freshening,
    interaction.template _ (List.mem_append_left _ (List.get_mem _ _))]
  exact Rigid.instantiate_include _ _

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem read_view (interaction : Interaction before) (position : Fin interaction.read.length) :
    (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows).read position =
        Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) (interaction.label (interaction.read.get position)) := by
  rw [ContextualActivatedStep.prepared_read_view]
  dsimp only [selection]
  rw [ContextualStoredRows.viewAt_eq_freshening,
    interaction.template _ (List.mem_append_right _ (List.get_mem _ _))]
  exact Rigid.instantiate_include _ _

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem actual_views (interaction : Interaction before) :
    List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows).taken =
        interaction.taken.map (Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) ∘ interaction.label) ∧
    List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows).read =
        interaction.read.map (Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) ∘ interaction.label) := by
  constructor
  · rw [show (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
        before.inventory.rows).taken = fun position => Rigid.includeTerm _ (interaction.label (interaction.taken.get position))
      from funext interaction.taken_view]
    exact List.ofFn_getElem_eq_map interaction.taken
      (Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) ∘ interaction.label)
  · rw [show (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
        before.inventory.rows).read = fun position => Rigid.includeTerm _ (interaction.label (interaction.read.get position))
      from funext interaction.read_view]
    exact List.ofFn_getElem_eq_map interaction.read
      (Rigid.includeTerm (ContextualActivatedStep.target locals before.declarations) ∘ interaction.label)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem use_same {V : Type} (declaration : V → MetaArity S) (label : O → Term S Γ sort) (selected : List O) :
    ContextualActivatedStep.useEquations (selected.map (Rigid.includeTerm declaration ∘ label))
      (selected.map (Rigid.includeTerm declaration ∘ label)) = diagonals declaration (selected.map label) := by
  induction selected with
  | nil => rfl
  | cons occurrence rest earlier =>
      change (_, _) :: ContextualActivatedStep.useEquations _ _ = (_, _) :: diagonals _ _
      rw [earlier]
      rfl

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem problem_is_complete_diagonals (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    ContextualActivatedStep.problem locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows before.inventory.configuration =
        diagonals (ContextualActivatedStep.target locals before.declarations) (interaction.terms prior) := by
  have views := interaction.actual_views
  have takenPatterns : (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection
      interaction.rule before.inventory.rows).rule.take =
        interaction.taken.map (Rigid.includeTerm _ ∘ interaction.label) := by
    change (interaction.taken.map (Rigid.includeTerm _ ∘ interaction.label)).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    exact Rigid.instantiate_include _ _
  have readPatterns : (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection
      interaction.rule before.inventory.rows).rule.read =
        interaction.read.map (Rigid.includeTerm _ ∘ interaction.label) := by
    change (interaction.read.map (Rigid.includeTerm _ ∘ interaction.label)).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    exact Rigid.instantiate_include _ _
  unfold ContextualActivatedStep.problem
  dsimp only
  rw [views.1, views.2, takenPatterns, readPatterns, use_same, use_same]
  change ContextualFrameUnifier.mapProblem _ before.inventory.configuration.equations ++ _ ++ _ ++ [] = _
  rw [incoming, map_diagonals]
  simp only [terms, diagonals, List.map_append, List.append_nil]

def prepared (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Prepared locals before where
  rule := interaction.rule
  ruleCovered := interaction.rule_covered
  selection := interaction.selection
  outputs := interaction.outputs
  formation := by
    refine ⟨by simp [rule, selection], by simp [rule, selection], ?_⟩
    exact (List.map_map ..).symm
  resources := by
    apply (ContextualInteractionFactors.resources_iff interaction.outputs interaction.selection before.inventory.configuration.present).mpr
    refine ⟨interaction.take_distinct, interaction.distinct, ?_⟩
    exact ⟨interaction.take_available, interaction.read_available, interaction.take_read_apart, interaction.fresh,
      fun _ member => by cases member⟩
  fuel := 1
  update := by
    letI := before.equality
    exact ContextualFrameWorklist.normalizationUpdate (by
      rw [interaction.problem_is_complete_diagonals prior incoming]
      exact normalize_diagonals _ _)
  computed := by
    let _ := before.equality
    generalize_proofs normalization
    have model : ContextualResidual.Models (generator (ContextualActivatedStep.target locals before.declarations))
        (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals before.declarations before.occupied
          interaction.selection interaction.rule before.inventory.rows before.inventory.configuration)) := by
      apply (ContextualResidual.models_observeProblem _ _).mpr
      rw [interaction.problem_is_complete_diagonals prior incoming]
      exact models_diagonals _ (generator _) _
    rw [ContextualFrameWorklist.run_eq_local_on_model 1 _ _ (generator _) model]
    rw [ContextualFrameWorklist.runWithRefuter_normalized _ 0 _ [] normalization (by rfl)]
    rfl
  finished := rfl

def target (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :=
  (interaction.prepared prior incoming).target

theorem checks (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Checked locals (interaction.prepared prior incoming).questions := by intro question member; cases member

def firing (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Firing locals before (interaction.target prior incoming) :=
  (interaction.prepared prior incoming).firing (interaction.checks prior incoming)

theorem target_equations (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    (interaction.target prior incoming).inventory.configuration.equations =
      diagonals (interaction.target prior incoming).declarations (interaction.terms prior) := by
  change ContextualFrameUnifier.mapProblem _
    (ContextualActivatedStep.problem locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows before.inventory.configuration) = _
  rw [interaction.problem_is_complete_diagonals prior incoming, map_diagonals]
  rfl

theorem target_world (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    (interaction.target prior incoming).inventory.configuration.present =
      fire before.inventory.configuration.present (interaction.selection.commit (T := Unit)) := rfl

end Interaction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution
