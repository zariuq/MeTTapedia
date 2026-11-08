import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRunNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationProducers
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Actual selected execution over open captured row terms

Selected views may contain arbitrary contextual applications. Their patterns
use exactly the same captured term, so the joint equations are reflexive.
Private rule locals remain available in outputs. The source worklist really
normalizes and discharges every identical meta-root equation; its original
declaration family is obtained from that proved return.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOpenSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger
open ContextualReflexiveRun ContextualExecutionCommutationNames
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
  label : O → Term (signature S before.declarations) Γ sort
  template : ∀ occurrence ∈ taken ++ read,
    ContextualStoredRows.asTemplate locals before.declarations (before.inventory.rows occurrence) =
      instantiate (ContextualSelectionViews.capturedSource locals before.declarations) (label occurrence)

namespace Interaction

variable {before : Endpoint locals O Γ sort}

def selection (interaction : Interaction before) : Selection O := ⟨interaction.taken, interaction.read, interaction.made⟩
def scope (_interaction : Interaction before) := ContextualActivationScopes.start before.occupied
def rule (interaction : Interaction before) : RuleInstance
    (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort) :=
  ⟨interaction.taken.map (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) ∘ interaction.label),
    interaction.read.map (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) ∘ interaction.label),
    [], [], interaction.made.map interaction.value⟩
def outputs (interaction : Interaction before) : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort :=
  fun occurrence => ContextualFreshening.termAt locals before.declarations interaction.scope (interaction.value occurrence)
def terms (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort)) :=
  prior ++ interaction.taken.map interaction.label ++ interaction.read.map interaction.label
def activeTerms (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort)) :=
  (interaction.terms prior).map (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations))
def targetTerms (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort)) :=
  (interaction.terms prior).map (instantiate (intoCapture locals before.declarations))

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem physical (interaction : Interaction before) :
    Enabled (fun _ : O => ()) before.inventory.configuration.present (interaction.selection.commit (T := Unit)) :=
  ⟨interaction.take_available, interaction.read_available, interaction.take_read_apart, interaction.fresh,
    fun _ member => by cases member⟩

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem rule_covered (interaction : Interaction before) :
    RuleCovered (privateScopes before.scopes) before.occupied interaction.rule := by
  intro value member
  change value ∈ interaction.taken.map (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) ∘ interaction.label) ++
    interaction.read.map (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) ∘ interaction.label) ++ [] ++ [] ++
      interaction.made.map interaction.value at member
  simp only [List.append_nil, List.mem_append] at member
  rcases member with (taken | read) | produced
  · obtain ⟨occurrence, selected, rfl⟩ := List.mem_map.mp taken
    have bounded := before.covered.rows occurrence (interaction.take_available (by simpa using selected))
    change Covered (privateScopes before.scopes) before.occupied
      (ContextualStoredRows.asTemplate locals before.declarations (before.inventory.rows occurrence)) at bounded
    rw [interaction.template occurrence (List.mem_append_left _ selected)] at bounded
    exact bounded
  · obtain ⟨occurrence, selected, rfl⟩ := List.mem_map.mp read
    have bounded := before.covered.rows occurrence (interaction.read_available (by simpa using selected))
    change Covered (privateScopes before.scopes) before.occupied
      (ContextualStoredRows.asTemplate locals before.declarations (before.inventory.rows occurrence)) at bounded
    rw [interaction.template occurrence (List.mem_append_right _ selected)] at bounded
    exact bounded
  · obtain ⟨occurrence, selected, rfl⟩ := List.mem_map.mp produced
    exact interaction.covered occurrence selected

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem open_captured (scope : Nat) (value : Term (signature S before.declarations) Γ sort) :
    ContextualFreshening.termAt locals before.declarations scope
        (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) value) =
      instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) value :=
  (ContextualStoredRows.viewAt_eq_freshening locals before.declarations scope (.shared value)).symm

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem taken_view (interaction : Interaction before) (position : Fin interaction.taken.length) :
    (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).taken position =
      instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) (interaction.label (interaction.taken.get position)) := by
  rw [ContextualActivatedStep.prepared_taken_view]
  dsimp only [selection]
  rw [ContextualStoredRows.viewAt_eq_freshening,
    interaction.template _ (List.mem_append_left _ (List.get_mem _ _))]
  exact open_captured _ _

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem read_view (interaction : Interaction before) (position : Fin interaction.read.length) :
    (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).read position =
      instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) (interaction.label (interaction.read.get position)) := by
  rw [ContextualActivatedStep.prepared_read_view]
  dsimp only [selection]
  rw [ContextualStoredRows.viewAt_eq_freshening,
    interaction.template _ (List.mem_append_right _ (List.get_mem _ _))]
  exact open_captured _ _

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem actual_views (interaction : Interaction before) :
    List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).taken =
      interaction.taken.map (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) ∘ interaction.label) ∧
    List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).read =
      interaction.read.map (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) ∘ interaction.label) := by
  constructor
  · rw [show (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).taken =
        fun position => instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) (interaction.label (interaction.taken.get position))
      from funext interaction.taken_view]
    simpa only [List.get_eq_getElem, Function.comp_def] using
      (List.ofFn_getElem_eq_map interaction.taken
        (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) ∘ interaction.label))
  · rw [show (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).read =
        fun position => instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) (interaction.label (interaction.read.get position))
      from funext interaction.read_view]
    simpa only [List.get_eq_getElem, Function.comp_def] using
      (List.ofFn_getElem_eq_map interaction.read
        (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) ∘ interaction.label))

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem use_same {V : Type} {declaration : V → MetaArity S}
    (values : List (Term (signature S declaration) Γ sort)) :
    ContextualActivatedStep.useEquations values values = termDiagonals values := by
  induction values with
  | nil => rfl
  | cons head tail earlier =>
      change (head, head) :: ContextualActivatedStep.useEquations tail tail =
        (head, head) :: termDiagonals tail
      exact congrArg (List.cons (head, head)) earlier

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem problem_is_complete_diagonals (interaction : Interaction before)
    (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :
    ContextualActivatedStep.problem locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows before.inventory.configuration = termDiagonals (interaction.activeTerms prior) := by
  have views := interaction.actual_views
  have patterns (selected : List O) :
      (selected.map (instantiate (ContextualSelectionViews.capturedSource locals before.declarations) ∘ interaction.label)).map
          (ContextualFreshening.termAt locals before.declarations interaction.scope) =
        selected.map (instantiate (ContextualSelectionViews.capturedTarget locals before.declarations) ∘ interaction.label) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    exact open_captured _ _
  have takes := patterns interaction.taken
  have reads := patterns interaction.read
  change (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).rule.take = _ at takes
  change (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule before.inventory.rows).rule.read = _ at reads
  unfold ContextualActivatedStep.problem
  dsimp only
  rw [views.1, views.2, takes, reads, use_same, use_same]
  change ContextualFrameUnifier.mapProblem _ before.inventory.configuration.equations ++ _ ++ _ ++ [] = _
  rw [incoming, map_termDiagonals]
  simp only [activeTerms, terms, termDiagonals, List.map_append, List.map_map, List.append_nil]

def prepared (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) : Prepared locals before where
  rule := interaction.rule
  ruleCovered := interaction.rule_covered
  selection := interaction.selection
  outputs := interaction.outputs
  formation := by
    refine ⟨by simp [rule, selection], by simp [rule, selection], ?_⟩
    exact (List.map_map ..).symm
  resources := by
    apply (ContextualInteractionFactors.resources_iff interaction.outputs interaction.selection before.inventory.configuration.present).mpr
    exact ⟨interaction.take_distinct, interaction.distinct, interaction.take_available, interaction.read_available,
      interaction.take_read_apart, interaction.fresh, fun _ member => by cases member⟩
  fuel := fuel (interaction.activeTerms prior)
  update := by
    letI := before.equality
    exact completedTerms _ (interaction.activeTerms prior) (interaction.problem_is_complete_diagonals prior incoming)
  computed := by
    let _ := before.equality
    exact actual_term_run _ _ _
  finished := rfl

def target (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :=
  (interaction.prepared prior incoming).target

theorem checks (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :
    Checked locals (interaction.prepared prior incoming).questions := by intro question member; cases member

def firing (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) : Firing locals before (interaction.target prior incoming) :=
  (interaction.prepared prior incoming).firing (interaction.checks prior incoming)

theorem capture_through_return (interaction : Interaction before)
    (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :
    Assignment.compose (ContextualComputedFreshFrame.includeSource (interaction.prepared prior incoming).update)
      (ContextualSelectionViews.capturedTarget locals before.declarations) = intoCapture locals before.declarations := by
  funext name
  change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations) (Sum.inr name)) = _
  rw [instantiate_generator, ContextualFreshFrameScopeLedger.includeSource_image]
  rfl

theorem target_equations (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :
    (interaction.target prior incoming).inventory.configuration.equations = termDiagonals (interaction.targetTerms prior) := by
  change ContextualFrameUnifier.mapProblem _
    (ContextualActivatedStep.problem locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows before.inventory.configuration) = _
  rw [interaction.problem_is_complete_diagonals prior incoming, map_termDiagonals]
  apply congrArg termDiagonals
  rw [activeTerms, List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, ← Assignment.instantiate_compose, capture_through_return]

theorem target_world (interaction : Interaction before) (prior : List (Term (signature S before.declarations) Γ sort))
    (incoming : before.inventory.configuration.equations = termDiagonals prior) :
    (interaction.target prior incoming).inventory.configuration.present =
      fire before.inventory.configuration.present (interaction.selection.commit (T := Unit)) := rfl

end Interaction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOpenSelectedExecution
