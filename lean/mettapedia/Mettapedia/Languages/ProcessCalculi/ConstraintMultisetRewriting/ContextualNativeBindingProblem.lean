import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleInputModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking

/-!
# A source-transparent control row and the native net-input binding problem

The entry inventory extends the source declarations by unused private
declarations. The compiled equations remain latent in one invocation row.
Consuming that row joins them with the conditions of the selected initial
inputs. Every input has a separate private bank, while its captures use
the current source block. Other stored conditions remain dormant.

Output and guard syntax are parameters of the binding result: they do not
alter the matching equations. Their publication and admission comparisons
remain separate obligations. The control row is explicit invocation data;
entry preparation is not equality of whole inventories. The firing takes
the control after its data takes, completing that selected invocation.
The comparison fixes the compiled physical selection. Alternative rule
selections and arbitrary program contexts require their own comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def bindingVariables (_schedule : Schedule S O Γ sort before after) : Option O → Type
  | none => Unit
  | some _ => First

def bindingDeclarations (schedule : Schedule S O Γ sort before after) :
    ∀ index, schedule.bindingVariables index → MetaArity S
  | none => fun _ => ⟨Γ, sort⟩
  | some _ => first

abbrev bindingLocals (schedule : Schedule S O Γ sort before after) :=
  ContextualConditionalRowPacking.family schedule.bindingVariables schedule.bindingDeclarations

def bindingCurrent (schedule : Schedule S O Γ sort before after) :
    Assignment after.declarations schedule.guardFamily :=
  ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inl none)

def bindingCaptures (schedule : Schedule S O Γ sort before after) :
    Assignment before.declarations schedule.guardFamily :=
  Assignment.compose schedule.bindingCurrent schedule.frame.assignment

abbrev bindingCurrentFrame (schedule : Schedule S O Γ sort before after) :
    ContextualGuardMatching.Extension after.declarations where
  Names := ContextualAnswerFamilies.Names schedule.guardVariables
  declarations := schedule.guardFamily
  name := fun name => ⟨.inl none, name⟩
  injective := by
    intro left right same
    exact eq_of_heq (Sigma.mk.inj same).2
  preserves _ := rfl

abbrev bindingFrame (schedule : Schedule S O Γ sort before after) :
    ContextualGuardMatching.Extension before.declarations :=
  schedule.frame.trans schedule.bindingCurrentFrame

theorem binding_frame_assignment (schedule : Schedule S O Γ sort before after) :
    schedule.bindingFrame.assignment = schedule.bindingCaptures :=
  ContextualGuardMatching.Extension.trans_assignment schedule.frame schedule.bindingCurrentFrame

def bindingControl (schedule : Schedule S O Γ sort before after) :
    Row schedule.bindingLocals schedule.guardFamily Γ sort :=
  ContextualConditionalRowPacking.pack schedule.bindingVariables schedule.bindingDeclarations schedule.guardFamily none
    ⟨.schema (generator (ContextualSelectionViews.source (schedule.bindingDeclarations none) schedule.guardFamily) (.inl ())),
      ContextualResidual.mapProblem
        (ContextualSelectionViews.capturedSource (schedule.bindingDeclarations none) schedule.guardFamily)
        schedule.guardProblem⟩

def bindingInput (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Row schedule.bindingLocals schedule.guardFamily Γ sort :=
  ContextualConditionalRowPacking.pack schedule.bindingVariables schedule.bindingDeclarations schedule.guardFamily (some occurrence)
    ((before.rows occurrence).map first before.declarations schedule.bindingCaptures)

def bindingRows (schedule : Schedule S O Γ sort before after) :
    Option (OccurrenceAllocationRenaming.Name O) → Row schedule.bindingLocals schedule.guardFamily Γ sort
  | none => schedule.bindingControl
  | some physical => schedule.bindingInput (OccurrenceAllocationRenaming.erase physical)

noncomputable def bindingSelection (schedule : Schedule S O Γ sort before after) :
    Selection (Option (OccurrenceAllocationRenaming.Name O)) :=
  ⟨schedule.net.effect.taken.toList.map some ++ [none],
    schedule.net.effect.kept.toList.map some,
    schedule.net.effect.made.toList.map some⟩

def bindingPattern (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort :=
  ContextualStoredRows.asTemplate schedule.bindingLocals schedule.guardFamily (schedule.bindingRows physical).value

noncomputable def bindingRule (schedule : Schedule S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :
    RuleInstance (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort) :=
  ⟨schedule.bindingSelection.taken.map schedule.bindingPattern,
    schedule.bindingSelection.read.map schedule.bindingPattern, [], guards, produced⟩

def bindingEntryProblem (schedule : Schedule S O Γ sort before after) :
    ContextualResidual.Problem schedule.guardFamily :=
  ContextualResidual.mapProblem schedule.bindingCaptures before.equations

private theorem packing_valuation {Index Shared Future : Type} (Variables : Index → Type)
    (locals : ∀ index, Variables index → MetaArity S) (captures : Shared → MetaArity S)
    {future : Future → MetaArity S} (index : Index)
    (images : Assignment (ContextualConditionalRowPacking.family Variables locals) future)
    (candidate : Assignment captures future) :
    Assignment.compose (valuation (ContextualConditionalRowPacking.family Variables locals) captures images candidate)
      (ContextualConditionalRowPacking.inclusion Variables locals captures index) =
      valuation (locals index) captures (fun name => images ⟨index, name⟩) candidate := by
  funext name
  cases name <;> exact instantiate_generator _ _

theorem binding_control_models (schedule : Schedule S O Γ sort before after)
    (images : Assignment schedule.bindingLocals next) (candidate : Assignment schedule.guardFamily next) :
    ContextualResidual.Models (valuation schedule.bindingLocals schedule.guardFamily images candidate)
        schedule.bindingControl.obligations ↔ ContextualResidual.Models candidate schedule.guardProblem := by
  change ContextualResidual.Models _ (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)) ↔ _
  rw [ContextualResidual.models_mapProblem, packing_valuation,
    ContextualResidual.models_mapProblem, valuation_captures]

theorem binding_input_models (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (images : Assignment schedule.bindingLocals next) (candidate : Assignment schedule.guardFamily next) :
    ContextualResidual.Models (valuation schedule.bindingLocals schedule.guardFamily images candidate)
        (schedule.bindingInput occurrence).obligations ↔
      ContextualResidual.Models
        (valuation first before.declarations (fun name => images ⟨some occurrence, name⟩)
          (Assignment.compose candidate schedule.bindingCaptures)) (before.rows occurrence).obligations := by
  change ContextualResidual.Models _ (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)) ↔ _
  erw [ContextualResidual.models_mapProblem, packing_valuation,
    ContextualResidual.models_mapProblem, valuation_capture_map]
  rfl

theorem binding_current_model (schedule : Schedule S O Γ sort before after)
    (candidate : Assignment schedule.guardFamily next)
    (model : ContextualResidual.Models candidate schedule.guardProblem) :
    ContextualResidual.Models (Assignment.compose candidate schedule.bindingCurrent) after.equations := by
  have current := (ContextualIndependentProblems.models_iff schedule.guardVariables schedule.guardDeclarations
    schedule.guardConditions schedule.guardIndices candidate).mp model (.inl none)
      (schedule.guard_index_list_complete _)
  change ContextualResidual.Models _ schedule.currentProblem at current
  rw [currentProblem, ← schedule.final_equations] at current
  exact current

theorem binding_entry_model (schedule : Schedule S O Γ sort before after)
    (candidate : Assignment schedule.guardFamily next)
    (model : ContextualResidual.Models candidate schedule.guardProblem) :
    ContextualResidual.Models candidate schedule.bindingEntryProblem := by
  apply (ContextualResidual.models_mapProblem _ _ _).mpr
  rw [bindingCaptures, Assignment.compose_associative]
  exact schedule.model_at_entry _ (schedule.binding_current_model candidate model)

/-- Preparing the declaration frame does not yet impose the program's
latent equations. It preserves the source entry problem's solvability. -/
theorem binding_entry_solvable_iff (schedule : Schedule S O Γ sort before after) :
    ContextualConditionalExecution.Solvable schedule.bindingEntryProblem ↔
      ContextualConditionalExecution.Solvable before.equations := by
  change ContextualConditionalExecution.Solvable
    (ContextualResidual.mapProblem schedule.bindingCaptures before.equations) ↔ _
  rw [← schedule.binding_frame_assignment]
  exact ContextualConditionalNaturality.solvable_extension_iff schedule.bindingFrame before.equations

theorem binding_input_matches (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (candidate : Assignment schedule.guardFamily next) (pattern : Term (signature S next) Γ sort) :
    Matches schedule.bindingLocals schedule.guardFamily candidate pattern (schedule.bindingInput occurrence) ↔
      Matches first before.declarations (Assignment.compose candidate schedule.bindingCaptures)
        pattern (before.rows occurrence) := by
  erw [bindingInput, ContextualConditionalRowPacking.matches_iff]
  exact matches_map_iff first before.declarations schedule.bindingCaptures candidate pattern (before.rows occurrence)

/-- One actor assignment satisfies every selected input condition while
preserving the given model of the compiled information. -/
theorem binding_selected_conditions (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits)
    (candidate : Assignment schedule.guardFamily next)
    (model : ContextualResidual.Models candidate schedule.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ images : Assignment schedule.bindingLocals extension.declarations,
        ∀ physical, physical ∈ schedule.bindingSelection.taken ∨ physical ∈ schedule.bindingSelection.read →
          ContextualResidual.Models
            (valuation schedule.bindingLocals schedule.guardFamily images
              (Assignment.compose extension.assignment candidate)) (schedule.bindingRows physical).obligations := by
  classical
  have current := schedule.binding_current_model candidate model
  obtain ⟨extension, filler, realized⟩ := schedule.initial_inputs_realize_together shapes
    (Assignment.compose candidate schedule.bindingCurrent) current schedule.initialInputs.toList
    (fun occurrence member => Finset.mem_toList.mp member)
  have root : Assignment.compose (Assignment.compose candidate schedule.bindingCurrent) schedule.frame.assignment =
      Assignment.compose candidate schedule.bindingCaptures :=
    (Assignment.compose_associative schedule.frame.assignment schedule.bindingCurrent candidate).symm
  rw [root] at realized
  have conditions : ∀ occurrence ∈ schedule.initialInputs,
      ∃ images : Assignment first extension.declarations,
        ContextualResidual.Models
          (valuation first before.declarations images
            (Assignment.compose extension.assignment (Assignment.compose candidate schedule.bindingCaptures)))
          (before.rows occurrence).obligations := by
    intro occurrence used
    obtain ⟨_pattern, images, condition, _value⟩ := realized occurrence (Finset.mem_toList.mpr used)
    exact ⟨images, condition⟩
  let rowImages : O → Assignment first extension.declarations := fun occurrence =>
    if used : occurrence ∈ schedule.initialInputs then Classical.choose (conditions occurrence used) else filler
  have rowConditions (occurrence : O) (used : occurrence ∈ schedule.initialInputs) :
      ContextualResidual.Models
        (valuation first before.declarations (rowImages occurrence)
          (Assignment.compose extension.assignment (Assignment.compose candidate schedule.bindingCaptures)))
        (before.rows occurrence).obligations := by
    dsimp only [rowImages]
    rw [dif_pos used]
    exact Classical.choose_spec (conditions occurrence used)
  let extra := ContextualGuardMatching.Extension.withLocals (schedule.bindingDeclarations none) extension.declarations
  let combined := extension.trans extra
  let images : Assignment schedule.bindingLocals combined.declarations := fun name =>
    match name with
    | ⟨none, localName⟩ => generator extra.declarations (.inl localName)
    | ⟨some occurrence, localName⟩ => instantiate extra.assignment (rowImages occurrence localName)
  have imageAt (occurrence : O) : (fun name => images ⟨some occurrence, name⟩) =
      Assignment.compose extra.assignment (rowImages occurrence) := rfl
  have captureSquare :
      Assignment.compose (Assignment.compose combined.assignment candidate) schedule.bindingCaptures =
        Assignment.compose extra.assignment
          (Assignment.compose extension.assignment (Assignment.compose candidate schedule.bindingCaptures)) := by
    dsimp only [combined]
    rw [ContextualGuardMatching.Extension.trans_assignment]
    simp only [Assignment.compose_associative]
    rfl
  have inputConditions (occurrence : O) (used : occurrence ∈ schedule.initialInputs) :
      ContextualResidual.Models
        (valuation schedule.bindingLocals schedule.guardFamily images
          (Assignment.compose combined.assignment candidate)) (schedule.bindingInput occurrence).obligations := by
    apply (schedule.binding_input_models occurrence images _).mpr
    erw [imageAt occurrence, captureSquare, valuation_future]
    exact ContextualResidual.models_compose (rowConditions occurrence used) extra.assignment
  refine ⟨combined, images, ?_⟩
  intro physical used
  cases physical with
  | none =>
      exact (schedule.binding_control_models images _).mpr
        (ContextualResidual.models_compose model combined.assignment)
  | some physical =>
      have netUsed : physical ∈ schedule.net.effect.taken ∪ schedule.net.effect.kept := by
        rcases used with taken | kept
        · apply Finset.mem_union.mpr
          left
          simpa only [bindingSelection, List.mem_append, List.mem_singleton, Option.some_ne_none, or_false,
            List.mem_map, Option.some.injEq, exists_eq_right,
            Finset.mem_toList] using taken
        · apply Finset.mem_union.mpr
          right
          simpa only [bindingSelection, List.mem_map, Option.some.injEq, exists_eq_right, Finset.mem_toList] using kept
      obtain ⟨occurrence, _present, rfl, initialUsed⟩ := schedule.net_input_is_initial resources physical netUsed
      exact inputConditions occurrence initialUsed

noncomputable def bindingInformation (schedule : Schedule S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :
    ContextualResidual.Problem (family schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) :=
  ContextualConditionalSourceProblem.problem schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
    schedule.bindingSelection (schedule.bindingRule produced guards) schedule.bindingRows schedule.bindingEntryProblem

/-- The control port makes every model of the binding problem project to
the compiled source information, independently of guard truth. -/
theorem binding_information_reflects (schedule : Schedule S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment (family schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) next)
    (model : ContextualResidual.Models candidate (schedule.bindingInformation produced guards)) :
    ContextualResidual.Models
      (ContextualClauseWitnesses.caller schedule.bindingLocals schedule.bindingLocals schedule.guardFamily candidate)
      schedule.guardProblem := by
  have latent := ((ContextualResidual.models_append candidate _ _).mp model).2
  have takes := ((ContextualClauseWitnesses.latent_models schedule.bindingLocals schedule.bindingLocals
    schedule.guardFamily candidate schedule.bindingSelection schedule.bindingRows).mp latent).1
  let control : Fin schedule.bindingSelection.taken.length :=
    ⟨(schedule.net.effect.taken.toList.map some).length, by simp only [bindingSelection, List.length_append, List.length_singleton]; omega⟩
  have selected : schedule.bindingSelection.taken.get control = none := by
    change (schedule.net.effect.taken.toList.map some ++ [none])[(schedule.net.effect.taken.toList.map some).length] = none
    exact List.getElem_of_append rfl rfl
  have conditions := takes control
  rw [selected] at conditions
  exact (schedule.binding_control_models _ _).mp conditions

private theorem get_mapped {A B : Type} (values : List A) (f : A → B) (port : Fin values.length) :
    (values.map f).get ⟨port.val, by simpa only [List.length_map] using port.isLt⟩ = f (values.get port) := by
  simp only [List.get_eq_getElem, List.getElem_map]

/-- Every particular compiled source model extends through all the actual
source port equations. Caller assignments are fixed by an injective frame. -/
theorem binding_information_extends (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment schedule.guardFamily next)
    (model : ContextualResidual.Models candidate schedule.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment (family schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) extension.declarations,
        ContextualResidual.Models combined (schedule.bindingInformation produced guards) ∧
          ContextualClauseWitnesses.caller schedule.bindingLocals schedule.bindingLocals schedule.guardFamily combined =
            Assignment.compose extension.assignment candidate := by
  obtain ⟨extension, images, conditions⟩ := schedule.binding_selected_conditions shapes resources candidate model
  have takeShape : (schedule.bindingRule produced guards).take.length = schedule.bindingSelection.taken.length :=
    List.length_map ..
  have readShape : (schedule.bindingRule produced guards).read.length = schedule.bindingSelection.read.length :=
    List.length_map ..
  let witness : ContextualClauseWitnesses.Witness schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
      schedule.bindingSelection (schedule.bindingRule produced guards) schedule.bindingRows schedule.bindingEntryProblem
      takeShape readShape extension.declarations := by
    refine ⟨images, Assignment.compose extension.assignment candidate, images,
      ContextualResidual.models_compose (schedule.binding_entry_model candidate model) extension.assignment,
      ?_, ?_, ?_⟩
    · intro equation member
      cases member
    · intro port
      refine ⟨images, conditions _ (.inl (List.get_mem _ _)), ?_⟩
      exact (congrArg (instantiate
        (valuation schedule.bindingLocals schedule.guardFamily images (Assignment.compose extension.assignment candidate)))
        (get_mapped schedule.bindingSelection.taken schedule.bindingPattern port)).symm
    · intro port
      refine ⟨images, conditions _ (.inr (List.get_mem _ _)), ?_⟩
      exact (congrArg (instantiate
        (valuation schedule.bindingLocals schedule.guardFamily images (Assignment.compose extension.assignment candidate)))
        (get_mapped schedule.bindingSelection.read schedule.bindingPattern port)).symm
  obtain ⟨combined, solved, _query, caller⟩ := witness.gives_model
    schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
  exact ⟨extension, combined, solved, caller⟩

def bindingState (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :
    ContextualConditionalExecution.State schedule.bindingLocals (Option (OccurrenceAllocationRenaming.Name O)) Γ sort where
  Names := ContextualAnswerFamilies.Names schedule.guardVariables
  equality := schedule.guardEquality
  declarations := schedule.guardFamily
  occupied := occupied
  equations := schedule.bindingEntryProblem
  present := insert none (before.present.image (fun occurrence => some (Sum.inl occurrence)))
  rows := schedule.bindingRows

noncomputable def nativeBindingRule (schedule : Schedule S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :=
  ContextualClauseProblem.nativeRule schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
    (schedule.bindingRule produced guards)

abbrev nativeBindingState (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :=
  ContextualConditionalSourceProblem.prepareState schedule.bindingLocals schedule.bindingLocals
    (schedule.bindingState occupied)

noncomputable def nativeBindingInformation (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :=
  ContextualConditionalExecution.information
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily occupied
    schedule.bindingSelection (schedule.nativeBindingRule produced guards) (schedule.nativeBindingState occupied).rows
    (schedule.nativeBindingState occupied).equations

theorem native_binding_information_eq (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :
    schedule.nativeBindingInformation occupied produced guards =
      ContextualResidual.mapProblem
        (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (schedule.bindingInformation produced guards) :=
  ContextualConditionalSourceProblem.actual_information schedule.bindingLocals schedule.bindingLocals
    schedule.guardFamily occupied schedule.bindingSelection (schedule.bindingRule produced guards)
    schedule.bindingRows schedule.bindingEntryProblem

/-- Every actual native binding model reflects the compiled source problem. -/
theorem native_binding_model_reflects (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment
      (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) next)
    (model : ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards)) :
    ContextualResidual.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget
        (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
      schedule.guardProblem := by
  rw [schedule.native_binding_information_eq occupied produced guards] at model
  have projected := (ContextualResidual.models_mapProblem _ _ _).mp model
  have reflected := schedule.binding_information_reflects produced guards _ projected
  rw [← ContextualClauseWitnesses.captures_square, ← Assignment.compose_associative,
    ContextualClauseFrames.captures_square] at reflected
  exact reflected

/-- The matching equations of the existing native step add no constraint
to a given compiled source model beyond fresh declaration names. -/
theorem native_binding_model_extends (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment schedule.guardFamily next)
    (model : ContextualResidual.Models candidate schedule.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment
        (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)
        extension.declarations,
        ContextualResidual.Models combined (schedule.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose combined (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily) =
              Assignment.compose extension.assignment candidate := by
  obtain ⟨extension, source, sourceModel, sourceCaller⟩ :=
    schedule.binding_information_extends shapes resources produced guards candidate model
  let frame := ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied
  let extra := ContextualGuardMatching.Extension.withLocals frame.complementDeclarations extension.declarations
  refine ⟨extension.trans extra, frame.liftModel source, ?_, ?_⟩
  · rw [schedule.native_binding_information_eq occupied produced guards]
    exact (ContextualConditionalNaturality.models_liftModel_iff frame source _).mpr sourceModel
  · erw [← ContextualClauseFrames.captures_square schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied,
      Assignment.compose_associative, frame.liftModel_square,
      ← Assignment.compose_associative, ContextualClauseWitnesses.captures_square, sourceCaller,
      ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
    rfl

/-- Adding saved birth and guard blocks preserves each particular terminal
model. No success judgment for an earlier guard is required. -/
theorem binding_guard_model_extends (schedule : Schedule S O Γ sort before after)
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment schedule.guardFamily extension.declarations,
        ContextualResidual.Models combined schedule.guardProblem ∧
          Assignment.compose combined schedule.bindingCurrent = Assignment.compose extension.assignment candidate := by
  have consistent : ContextualConditionalExecution.Solvable after.equations := ⟨Next, next, candidate, model⟩
  have current : ContextualResidual.Models candidate (schedule.guardConditions (.inl none)) := by
    change ContextualResidual.Models candidate schedule.currentProblem
    rw [currentProblem, ← schedule.final_equations]
    exact model
  exact ContextualIndependentProblems.extend_model schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
    (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inl none) candidate current

/-- Every source model extends through the complete actual native binding
problem, fixing its full current assignment up to fresh-name inclusion. -/
theorem source_model_extends_native_binding (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment
        (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)
        extension.declarations,
        ContextualResidual.Models combined (schedule.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose
            (Assignment.compose combined (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
            schedule.bindingCurrent = Assignment.compose extension.assignment candidate := by
  obtain ⟨blocks, guardModel, guarded, current⟩ := schedule.binding_guard_model_extends candidate model
  obtain ⟨ports, combined, solved, caller⟩ := schedule.native_binding_model_extends shapes resources occupied
    produced guards guardModel guarded
  refine ⟨blocks.trans ports, combined, solved, ?_⟩
  erw [caller, ← Assignment.compose_associative, current,
    ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
  rfl

theorem native_binding_solvable_iff (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))) :
    ContextualConditionalExecution.Solvable (schedule.nativeBindingInformation occupied produced guards) ↔
      ContextualConditionalExecution.Solvable after.equations := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, _, schedule.binding_current_model _
      (schedule.native_binding_model_reflects occupied produced guards candidate model)⟩
  · rintro ⟨Future, future, candidate, model⟩
    obtain ⟨extension, combined, solved, _fixed⟩ :=
      schedule.source_model_extends_native_binding shapes resources occupied produced guards candidate model
    exact ⟨extension.Names, extension.declarations, combined, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
