import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses
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
The construction is stated once over compiled bodies; ordinary/shared and
mixed captured-template schedules are instances.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def bindingVariables (_body : Body S O Γ sort before after) : Option O → Type
  | none => Unit
  | some _ => First

def bindingDeclarations (body : Body S O Γ sort before after) :
    ∀ index, body.bindingVariables index → MetaArity S
  | none => fun _ => ⟨Γ, sort⟩
  | some _ => first

abbrev bindingLocals (body : Body S O Γ sort before after) :=
  ContextualConditionalRowPacking.family body.bindingVariables body.bindingDeclarations

instance bindingEquality (body : Body S O Γ sort before after) [DecidableEq First] :
    DecidableEq (ContextualAnswerFamilies.Names body.bindingVariables) := by
  let _ : ∀ index, DecidableEq (body.bindingVariables index) := fun index =>
    match index with
    | none => inferInstanceAs (DecidableEq Unit)
    | some _ => inferInstanceAs (DecidableEq First)
  infer_instance

def bindingCurrent (body : Body S O Γ sort before after) :
    Assignment after.declarations body.guardFamily :=
  ContextualIndependentProblems.inclusion body.guardVariables body.guardDeclarations (.inl none)

def bindingCaptures (body : Body S O Γ sort before after) :
    Assignment before.declarations body.guardFamily :=
  Assignment.compose body.bindingCurrent body.frame.assignment

abbrev bindingCurrentFrame (body : Body S O Γ sort before after) :
    ContextualGuardMatching.Extension after.declarations where
  Names := ContextualAnswerFamilies.Names body.guardVariables
  declarations := body.guardFamily
  name := fun name => ⟨.inl none, name⟩
  injective := by
    intro left right same
    exact eq_of_heq (Sigma.mk.inj same).2
  preserves _ := rfl

abbrev bindingFrame (body : Body S O Γ sort before after) :
    ContextualGuardMatching.Extension before.declarations :=
  body.frame.trans body.bindingCurrentFrame

theorem binding_frame_assignment (body : Body S O Γ sort before after) :
    body.bindingFrame.assignment = body.bindingCaptures :=
  ContextualGuardMatching.Extension.trans_assignment body.frame body.bindingCurrentFrame

def bindingControl (body : Body S O Γ sort before after) :
    Row body.bindingLocals body.guardFamily Γ sort :=
  ContextualConditionalRowPacking.pack body.bindingVariables body.bindingDeclarations body.guardFamily none
    ⟨.schema (generator (ContextualSelectionViews.source (body.bindingDeclarations none) body.guardFamily) (.inl ())),
      ContextualResidual.mapProblem
        (ContextualSelectionViews.capturedSource (body.bindingDeclarations none) body.guardFamily)
        body.guardProblem⟩

def bindingInput (body : Body S O Γ sort before after) (occurrence : O) :
    Row body.bindingLocals body.guardFamily Γ sort :=
  ContextualConditionalRowPacking.pack body.bindingVariables body.bindingDeclarations body.guardFamily (some occurrence)
    ((before.rows occurrence).map first before.declarations body.bindingCaptures)

def bindingRows (body : Body S O Γ sort before after) :
    Option (OccurrenceAllocationRenaming.Name O) → Row body.bindingLocals body.guardFamily Γ sort
  | none => body.bindingControl
  | some physical => body.bindingInput (OccurrenceAllocationRenaming.erase physical)

noncomputable def bindingSelection (body : Body S O Γ sort before after) :
    Selection (Option (OccurrenceAllocationRenaming.Name O)) :=
  ⟨body.net.effect.taken.toList.map some ++ [none],
    body.net.effect.kept.toList.map some,
    body.net.effect.made.toList.map some⟩

def bindingPattern (body : Body S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort :=
  ContextualStoredRows.asTemplate body.bindingLocals body.guardFamily (body.bindingRows physical).value

noncomputable def bindingRule (body : Body S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :
    RuleInstance (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort) :=
  ⟨body.bindingSelection.taken.map body.bindingPattern,
    body.bindingSelection.read.map body.bindingPattern, [], guards, produced⟩

def bindingEntryProblem (body : Body S O Γ sort before after) :
    ContextualResidual.Problem body.guardFamily :=
  ContextualResidual.mapProblem body.bindingCaptures before.equations

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

theorem binding_control_models (body : Body S O Γ sort before after)
    (images : Assignment body.bindingLocals next) (candidate : Assignment body.guardFamily next) :
    ContextualResidual.Models (valuation body.bindingLocals body.guardFamily images candidate)
        body.bindingControl.obligations ↔ ContextualResidual.Models candidate body.guardProblem := by
  change ContextualResidual.Models _ (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)) ↔ _
  rw [ContextualResidual.models_mapProblem, packing_valuation,
    ContextualResidual.models_mapProblem, valuation_captures]

theorem binding_input_models (body : Body S O Γ sort before after) (occurrence : O)
    (images : Assignment body.bindingLocals next) (candidate : Assignment body.guardFamily next) :
    ContextualResidual.Models (valuation body.bindingLocals body.guardFamily images candidate)
        (body.bindingInput occurrence).obligations ↔
      ContextualResidual.Models
        (valuation first before.declarations (fun name => images ⟨some occurrence, name⟩)
          (Assignment.compose candidate body.bindingCaptures)) (before.rows occurrence).obligations := by
  change ContextualResidual.Models _ (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)) ↔ _
  erw [ContextualResidual.models_mapProblem, packing_valuation,
    ContextualResidual.models_mapProblem, valuation_capture_map]
  rfl

theorem binding_current_model (body : Body S O Γ sort before after)
    (candidate : Assignment body.guardFamily next)
    (model : ContextualResidual.Models candidate body.guardProblem) :
    ContextualResidual.Models (Assignment.compose candidate body.bindingCurrent) after.equations := by
  have current := (ContextualIndependentProblems.models_iff body.guardVariables body.guardDeclarations
    body.guardConditions body.guardIndices candidate).mp model (.inl none)
      body.guard_index_current_listed
  change ContextualResidual.Models _ body.currentProblem at current
  rw [body.current_problem_eq] at current
  exact current

theorem binding_entry_model (body : Body S O Γ sort before after)
    (candidate : Assignment body.guardFamily next)
    (model : ContextualResidual.Models candidate body.guardProblem) :
    ContextualResidual.Models candidate body.bindingEntryProblem := by
  apply (ContextualResidual.models_mapProblem _ _ _).mpr
  rw [bindingCaptures, Assignment.compose_associative]
  exact body.model_at_entry _ (body.binding_current_model candidate model)

/-- Preparing the declaration frame does not yet impose the program's
latent equations. It preserves the source entry problem's solvability. -/
theorem binding_entry_solvable_iff (body : Body S O Γ sort before after) :
    ContextualConditionalExecution.Solvable body.bindingEntryProblem ↔
      ContextualConditionalExecution.Solvable before.equations := by
  change ContextualConditionalExecution.Solvable
    (ContextualResidual.mapProblem body.bindingCaptures before.equations) ↔ _
  rw [← body.binding_frame_assignment]
  exact ContextualConditionalNaturality.solvable_extension_iff body.bindingFrame before.equations

theorem binding_input_matches (body : Body S O Γ sort before after) (occurrence : O)
    (candidate : Assignment body.guardFamily next) (pattern : Term (signature S next) Γ sort) :
    Matches body.bindingLocals body.guardFamily candidate pattern (body.bindingInput occurrence) ↔
      Matches first before.declarations (Assignment.compose candidate body.bindingCaptures)
        pattern (before.rows occurrence) := by
  erw [bindingInput, ContextualConditionalRowPacking.matches_iff]
  exact matches_map_iff first before.declarations body.bindingCaptures candidate pattern (before.rows occurrence)

/-- One actor assignment satisfies every selected input condition while
preserving the given model of the compiled information. -/
theorem binding_selected_conditions (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (candidate : Assignment body.guardFamily next)
    (model : ContextualResidual.Models candidate body.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ images : Assignment body.bindingLocals extension.declarations,
        ∀ physical, physical ∈ body.bindingSelection.taken ∨ physical ∈ body.bindingSelection.read →
          ContextualResidual.Models
            (valuation body.bindingLocals body.guardFamily images
              (Assignment.compose extension.assignment candidate)) (body.bindingRows physical).obligations := by
  classical
  have current := body.binding_current_model candidate model
  obtain ⟨extension, filler, realized⟩ := body.initial_inputs_realize_together shapes
    (Assignment.compose candidate body.bindingCurrent) current body.initialInputs.toList
    (fun occurrence member => Finset.mem_toList.mp member)
  have root : Assignment.compose (Assignment.compose candidate body.bindingCurrent) body.frame.assignment =
      Assignment.compose candidate body.bindingCaptures :=
    (Assignment.compose_associative body.frame.assignment body.bindingCurrent candidate).symm
  rw [root] at realized
  have conditions : ∀ occurrence ∈ body.initialInputs,
      ∃ images : Assignment first extension.declarations,
        ContextualResidual.Models
          (valuation first before.declarations images
            (Assignment.compose extension.assignment (Assignment.compose candidate body.bindingCaptures)))
          (before.rows occurrence).obligations := by
    intro occurrence used
    obtain ⟨_pattern, images, condition, _value⟩ := realized occurrence (Finset.mem_toList.mpr used)
    exact ⟨images, condition⟩
  let rowImages : O → Assignment first extension.declarations := fun occurrence =>
    if used : occurrence ∈ body.initialInputs then Classical.choose (conditions occurrence used) else filler
  have rowConditions (occurrence : O) (used : occurrence ∈ body.initialInputs) :
      ContextualResidual.Models
        (valuation first before.declarations (rowImages occurrence)
          (Assignment.compose extension.assignment (Assignment.compose candidate body.bindingCaptures)))
        (before.rows occurrence).obligations := by
    dsimp only [rowImages]
    rw [dif_pos used]
    exact Classical.choose_spec (conditions occurrence used)
  let extra := ContextualGuardMatching.Extension.withLocals (body.bindingDeclarations none) extension.declarations
  let combined := extension.trans extra
  let images : Assignment body.bindingLocals combined.declarations := fun name =>
    match name with
    | ⟨none, localName⟩ => generator extra.declarations (.inl localName)
    | ⟨some occurrence, localName⟩ => instantiate extra.assignment (rowImages occurrence localName)
  have imageAt (occurrence : O) : (fun name => images ⟨some occurrence, name⟩) =
      Assignment.compose extra.assignment (rowImages occurrence) := rfl
  have captureSquare :
      Assignment.compose (Assignment.compose combined.assignment candidate) body.bindingCaptures =
        Assignment.compose extra.assignment
          (Assignment.compose extension.assignment (Assignment.compose candidate body.bindingCaptures)) := by
    dsimp only [combined]
    rw [ContextualGuardMatching.Extension.trans_assignment]
    simp only [Assignment.compose_associative]
    rfl
  have inputConditions (occurrence : O) (used : occurrence ∈ body.initialInputs) :
      ContextualResidual.Models
        (valuation body.bindingLocals body.guardFamily images
          (Assignment.compose combined.assignment candidate)) (body.bindingInput occurrence).obligations := by
    apply (body.binding_input_models occurrence images _).mpr
    erw [imageAt occurrence, captureSquare, valuation_future]
    exact ContextualResidual.models_compose (rowConditions occurrence used) extra.assignment
  refine ⟨combined, images, ?_⟩
  intro physical used
  cases physical with
  | none =>
      exact (body.binding_control_models images _).mpr
        (ContextualResidual.models_compose model combined.assignment)
  | some physical =>
      have netUsed : physical ∈ body.net.effect.taken ∪ body.net.effect.kept := by
        rcases used with taken | kept
        · apply Finset.mem_union.mpr
          left
          simpa only [bindingSelection, List.mem_append, List.mem_singleton, Option.some_ne_none, or_false,
            List.mem_map, Option.some.injEq, exists_eq_right,
            Finset.mem_toList] using taken
        · apply Finset.mem_union.mpr
          right
          simpa only [bindingSelection, List.mem_map, Option.some.injEq, exists_eq_right, Finset.mem_toList] using kept
      obtain ⟨occurrence, _present, rfl, initialUsed⟩ := body.net_input_is_initial resources physical netUsed
      exact inputConditions occurrence initialUsed

noncomputable def bindingInformation (body : Body S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :
    ContextualResidual.Problem (family body.bindingLocals body.bindingLocals body.guardFamily) :=
  ContextualConditionalSourceProblem.problem body.bindingLocals body.bindingLocals body.guardFamily
    body.bindingSelection (body.bindingRule produced guards) body.bindingRows body.bindingEntryProblem

/-- The control port makes every model of the binding problem project to
the compiled source information, independently of guard truth. -/
theorem binding_information_reflects (body : Body S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment (family body.bindingLocals body.bindingLocals body.guardFamily) next)
    (model : ContextualResidual.Models candidate (body.bindingInformation produced guards)) :
    ContextualResidual.Models
      (ContextualClauseWitnesses.caller body.bindingLocals body.bindingLocals body.guardFamily candidate)
      body.guardProblem := by
  have latent := ((ContextualResidual.models_append candidate _ _).mp model).2
  have takes := ((ContextualClauseWitnesses.latent_models body.bindingLocals body.bindingLocals
    body.guardFamily candidate body.bindingSelection body.bindingRows).mp latent).1
  let control : Fin body.bindingSelection.taken.length :=
    ⟨(body.net.effect.taken.toList.map some).length, by simp only [bindingSelection, List.length_append, List.length_singleton]; omega⟩
  have selected : body.bindingSelection.taken.get control = none := by
    change (body.net.effect.taken.toList.map some ++ [none])[(body.net.effect.taken.toList.map some).length] = none
    exact List.getElem_of_append rfl rfl
  have conditions := takes control
  rw [selected] at conditions
  exact (body.binding_control_models _ _).mp conditions

private theorem get_mapped {A B : Type} (values : List A) (f : A → B) (port : Fin values.length) :
    (values.map f).get ⟨port.val, by simpa only [List.length_map] using port.isLt⟩ = f (values.get port) := by
  simp only [List.get_eq_getElem, List.getElem_map]

/-- Every particular compiled source model extends through all the actual
source port equations. Caller assignments are fixed by an injective frame. -/
theorem binding_information_extends (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment body.guardFamily next)
    (model : ContextualResidual.Models candidate body.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment (family body.bindingLocals body.bindingLocals body.guardFamily) extension.declarations,
        ContextualResidual.Models combined (body.bindingInformation produced guards) ∧
          ContextualClauseWitnesses.caller body.bindingLocals body.bindingLocals body.guardFamily combined =
            Assignment.compose extension.assignment candidate := by
  obtain ⟨extension, images, conditions⟩ := body.binding_selected_conditions shapes resources candidate model
  have takeShape : (body.bindingRule produced guards).take.length = body.bindingSelection.taken.length :=
    List.length_map ..
  have readShape : (body.bindingRule produced guards).read.length = body.bindingSelection.read.length :=
    List.length_map ..
  let witness : ContextualClauseWitnesses.Witness body.bindingLocals body.bindingLocals body.guardFamily
      body.bindingSelection (body.bindingRule produced guards) body.bindingRows body.bindingEntryProblem
      takeShape readShape extension.declarations := by
    refine ⟨images, Assignment.compose extension.assignment candidate, images,
      ContextualResidual.models_compose (body.binding_entry_model candidate model) extension.assignment,
      ?_, ?_, ?_⟩
    · intro equation member
      cases member
    · intro port
      refine ⟨images, conditions _ (.inl (List.get_mem _ _)), ?_⟩
      exact (congrArg (instantiate
        (valuation body.bindingLocals body.guardFamily images (Assignment.compose extension.assignment candidate)))
        (get_mapped body.bindingSelection.taken body.bindingPattern port)).symm
    · intro port
      refine ⟨images, conditions _ (.inr (List.get_mem _ _)), ?_⟩
      exact (congrArg (instantiate
        (valuation body.bindingLocals body.guardFamily images (Assignment.compose extension.assignment candidate)))
        (get_mapped body.bindingSelection.read body.bindingPattern port)).symm
  obtain ⟨combined, solved, _query, caller⟩ := witness.gives_model
    body.bindingLocals body.bindingLocals body.guardFamily
  exact ⟨extension, combined, solved, caller⟩

def bindingState (body : Body S O Γ sort before after) (occupied : Finset Nat) :
    ContextualConditionalExecution.State body.bindingLocals (Option (OccurrenceAllocationRenaming.Name O)) Γ sort where
  Names := ContextualAnswerFamilies.Names body.guardVariables
  equality := body.guardEquality
  declarations := body.guardFamily
  occupied := occupied
  equations := body.bindingEntryProblem
  present := insert none (before.present.image (fun occurrence => some (Sum.inl occurrence)))
  rows := body.bindingRows

noncomputable def nativeBindingRule (body : Body S O Γ sort before after)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :=
  ContextualClauseProblem.nativeRule body.bindingLocals body.bindingLocals body.guardFamily
    (body.bindingRule produced guards)

abbrev nativeBindingState (body : Body S O Γ sort before after) (occupied : Finset Nat) :=
  ContextualConditionalSourceProblem.prepareState body.bindingLocals body.bindingLocals
    (body.bindingState occupied)

noncomputable def nativeBindingInformation (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :=
  ContextualConditionalExecution.information
    (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily occupied
    body.bindingSelection (body.nativeBindingRule produced guards) (body.nativeBindingState occupied).rows
    (body.nativeBindingState occupied).equations

theorem native_binding_information_eq (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :
    body.nativeBindingInformation occupied produced guards =
      ContextualResidual.mapProblem
        (ContextualClauseFrames.frame body.bindingLocals body.bindingLocals body.guardFamily occupied).assignment
        (body.bindingInformation produced guards) :=
  ContextualConditionalSourceProblem.actual_information body.bindingLocals body.bindingLocals
    body.guardFamily occupied body.bindingSelection (body.bindingRule produced guards)
    body.bindingRows body.bindingEntryProblem

/-- Every actual native binding model reflects the compiled source problem. -/
theorem native_binding_model_reflects (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment
      (ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily) next)
    (model : ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards)) :
    ContextualResidual.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget
        (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily))
      body.guardProblem := by
  rw [body.native_binding_information_eq occupied produced guards] at model
  have projected := (ContextualResidual.models_mapProblem _ _ _).mp model
  have reflected := body.binding_information_reflects produced guards _ projected
  rw [← ContextualClauseWitnesses.captures_square, ← Assignment.compose_associative,
    ContextualClauseFrames.captures_square] at reflected
  exact reflected

/-- The matching equations of the existing native step add no constraint
to a given compiled source model beyond fresh declaration names. -/
theorem native_binding_model_extends (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment body.guardFamily next)
    (model : ContextualResidual.Models candidate body.guardProblem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment
        (ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily)
        extension.declarations,
        ContextualResidual.Models combined (body.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose combined (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily) =
              Assignment.compose extension.assignment candidate := by
  obtain ⟨extension, source, sourceModel, sourceCaller⟩ :=
    body.binding_information_extends shapes resources produced guards candidate model
  let frame := ContextualClauseFrames.frame body.bindingLocals body.bindingLocals body.guardFamily occupied
  let extra := ContextualGuardMatching.Extension.withLocals frame.complementDeclarations extension.declarations
  refine ⟨extension.trans extra, frame.liftModel source, ?_, ?_⟩
  · rw [body.native_binding_information_eq occupied produced guards]
    exact (ContextualConditionalNaturality.models_liftModel_iff frame source _).mpr sourceModel
  · erw [← ContextualClauseFrames.captures_square body.bindingLocals body.bindingLocals body.guardFamily occupied,
      Assignment.compose_associative, frame.liftModel_square,
      ← Assignment.compose_associative, ContextualClauseWitnesses.captures_square, sourceCaller,
      ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
    rfl

/-- Adding saved birth and guard blocks preserves each particular terminal
model. No success judgment for an earlier guard is required. -/
theorem binding_guard_model_extends (body : Body S O Γ sort before after)
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment body.guardFamily extension.declarations,
        ContextualResidual.Models combined body.guardProblem ∧
          Assignment.compose combined body.bindingCurrent = Assignment.compose extension.assignment candidate := by
  have consistent : ContextualConditionalExecution.Solvable after.equations := ⟨Next, next, candidate, model⟩
  have current : ContextualResidual.Models candidate (body.guardConditions (.inl none)) := by
    change ContextualResidual.Models candidate body.currentProblem
    rw [body.current_problem_eq]
    exact model
  exact ContextualIndependentProblems.extend_model body.guardVariables body.guardDeclarations body.guardConditions
    (body.guard_blocks_solvable consistent) body.guardIndices (.inl none) candidate current

/-- Every source model extends through the complete actual native binding
problem, fixing its full current assignment up to fresh-name inclusion. -/
theorem source_model_extends_native_binding (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment
        (ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily)
        extension.declarations,
        ContextualResidual.Models combined (body.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose
            (Assignment.compose combined (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily))
            body.bindingCurrent = Assignment.compose extension.assignment candidate := by
  obtain ⟨blocks, guardModel, guarded, current⟩ := body.binding_guard_model_extends candidate model
  obtain ⟨ports, combined, solved, caller⟩ := body.native_binding_model_extends shapes resources occupied
    produced guards guardModel guarded
  refine ⟨blocks.trans ports, combined, solved, ?_⟩
  erw [caller, ← Assignment.compose_associative, current,
    ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
  rfl

theorem native_binding_solvable_iff (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))) :
    ContextualConditionalExecution.Solvable (body.nativeBindingInformation occupied produced guards) ↔
      ContextualConditionalExecution.Solvable after.equations := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, _, body.binding_current_model _
      (body.native_binding_model_reflects occupied produced guards candidate model)⟩
  · rintro ⟨Future, future, candidate, model⟩
    obtain ⟨extension, combined, solved, _fixed⟩ :=
      body.source_model_extends_native_binding shapes resources occupied produced guards candidate model
    exact ⟨extension.Names, extension.declarations, combined, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
