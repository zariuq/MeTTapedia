import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEntryGuardCompilation

/-!
# Actual native row labels interpreted at an original guard cut

The current caller and each saved guard cut have distinct declaration
blocks. Resetting the captures of an actual row to a saved block recovers
the original input's meaning at that cut. Schema-private names stay private.
Queries apply this reset to the row supplied by the current inventory;
they do not consult a captured source row dictionary.
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

def guardCutInclusion (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment after.declarations schedule.guardFamily :=
  ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inr index)

def guardCutReset (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment schedule.guardFamily schedule.guardFamily := fun name =>
  match name with
  | ⟨.inl none, name⟩ => generator schedule.guardFamily ⟨.inr index, name⟩
  | ⟨.inl (some birth), name⟩ => generator schedule.guardFamily ⟨.inl (some birth), name⟩
  | ⟨.inr cut, name⟩ => generator schedule.guardFamily ⟨.inr cut, name⟩

theorem guard_cut_reset_current (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment.compose (schedule.guardCutReset index) schedule.bindingCurrent = schedule.guardCutInclusion index := by
  funext name
  exact instantiate_generator _ _

theorem guard_cut_reset_captures (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment.compose (schedule.guardCutReset index) schedule.bindingCaptures =
      Assignment.compose (schedule.guardCutInclusion index) schedule.frame.assignment := by
  rw [bindingCaptures, Assignment.compose_associative, guard_cut_reset_current]

abbrev guardNativeBank (schedule : Schedule S O Γ sort before after) :=
  ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals

abbrev guardNativeFamily (schedule : Schedule S O Γ sort before after) :=
  ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily

abbrev guardNativeCaptures (schedule : Schedule S O Γ sort before after) :
    Assignment schedule.guardFamily schedule.guardNativeFamily :=
  ContextualSelectionViews.capturedTarget schedule.guardNativeBank schedule.guardFamily

def nativeGuardReset (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment schedule.guardNativeFamily schedule.guardNativeFamily
  | .inl name => generator schedule.guardNativeFamily (.inl name)
  | .inr name => instantiate schedule.guardNativeCaptures (schedule.guardCutReset index name)

theorem native_guard_reset_captures (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment.compose (schedule.nativeGuardReset index) schedule.guardNativeCaptures =
      Assignment.compose schedule.guardNativeCaptures (schedule.guardCutReset index) := by
  funext name
  exact instantiate_generator _ _

def nativeGuardCut (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment after.declarations schedule.guardNativeFamily :=
  Assignment.compose schedule.guardNativeCaptures (schedule.guardCutInclusion index)

theorem native_guard_reset_root (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Assignment.compose (schedule.nativeGuardReset index)
        (Assignment.compose schedule.guardNativeCaptures schedule.bindingCaptures) =
      Assignment.compose (schedule.nativeGuardCut index) schedule.frame.assignment := by
  rw [Assignment.compose_associative, native_guard_reset_captures,
    ← Assignment.compose_associative, guard_cut_reset_captures, Assignment.compose_associative]
  rfl

def nativeGuardRow (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (row : Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) :
    Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort :=
  row.map schedule.guardNativeBank schedule.guardNativeFamily (schedule.nativeGuardReset index)

/-- Resetting an actual prepared input label recovers its original caller
at the selected saved cut, including the row's latent private conditions. -/
theorem native_guard_input_matches (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat) (occurrence : O) (candidate : Assignment schedule.guardNativeFamily next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.guardNativeBank schedule.guardNativeFamily candidate pattern
      (schedule.nativeGuardRow index
        (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank
          (schedule.nativeBindingState occupied) (some (.inl occurrence))).2) ↔
      Matches first before.declarations
        (Assignment.compose (Assignment.compose candidate (schedule.nativeGuardCut index)) schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  change Matches _ _ candidate pattern
    (((ContextualConditionalExecution.guardRows schedule.guardNativeBank schedule.guardFamily
        (schedule.nativeBindingState occupied).rows (some (.inl occurrence))).map
      schedule.guardNativeBank schedule.guardNativeFamily (schedule.nativeGuardReset index))) ↔ _
  rw [matches_map_iff]
  change Matches _ _ (Assignment.compose candidate (schedule.nativeGuardReset index)) pattern
    ((ContextualConditionalPublication.extendPrivate schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
      (schedule.bindingInput occurrence)).map schedule.guardNativeBank schedule.guardFamily schedule.guardNativeCaptures) ↔ _
  rw [matches_map_iff, ContextualConditionalPublication.extendPrivate_matches_iff,
    binding_input_matches]
  have square :
      Assignment.compose
          (Assignment.compose (Assignment.compose candidate (schedule.nativeGuardReset index)) schedule.guardNativeCaptures)
          schedule.bindingCaptures =
        Assignment.compose (Assignment.compose candidate (schedule.nativeGuardCut index)) schedule.frame.assignment := by
    rw [← Assignment.compose_associative, ← Assignment.compose_associative,
      native_guard_reset_root, Assignment.compose_associative]
  rw [square]

abbrev GuardPhysical (O : Type) := Option (OccurrenceAllocationRenaming.Name O)

noncomputable def nativeCutMatchingQuery (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort)
    (excluded seen : Finset (GuardPhysical O)) :
    ContextualPredicateQueryAdmission.DataQuery schedule.guardNativeFamily
      (GuardPhysical O × Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O) := by
  classical
  exact ⟨(fun candidate label => decide (label.1 ≠ none ∧ label.1 ∉ excluded ∧
    Matches schedule.guardNativeBank schedule.guardNativeFamily candidate.assignment
      (instantiate candidate.assignment (instantiate (schedule.nativeGuardCut index) pattern))
      (schedule.nativeGuardRow index label.2))), seen⟩

def survivingGuardInputs (_schedule : Schedule S O Γ sort before after)
    (excluded : Finset (GuardPhysical O)) : Finset O :=
  before.present.filter fun occurrence => some (.inl occurrence) ∉ excluded

def sourceGuardInputs (schedule : Schedule S O Γ sort before after) : O → Row first after.declarations Γ sort :=
  fun occurrence => (before.rows occurrence).map first before.declarations schedule.frame.assignment

/-- The real query region is exactly the surviving entry matching region
at the saved cut. The program/control occurrence contributes no match. -/
theorem native_cut_query_region (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat) (pattern : Term (signature S after.declarations) Γ sort)
    (excluded seen : Finset (GuardPhysical O)) (candidate : Assignment schedule.guardNativeFamily next) :
    regionOf (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
        (schedule.nativeBindingState occupied).present
        ((schedule.nativeCutMatchingQuery index pattern excluded seen).region ⟨Next, next, candidate⟩) =
      (ContextualConditionalGuards.region first (Assignment.compose candidate (schedule.nativeGuardCut index))
        schedule.sourceGuardInputs (schedule.survivingGuardInputs excluded) pattern).image
        (fun occurrence => some (Sum.inl occurrence)) := by
  classical
  let label := ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)
  have view (occurrence : O) :
      Matches schedule.guardNativeBank schedule.guardNativeFamily candidate
          (instantiate candidate (instantiate (schedule.nativeGuardCut index) pattern))
          (schedule.nativeGuardRow index (label (some (.inl occurrence))).2) ↔
        Matches first after.declarations (Assignment.compose candidate (schedule.nativeGuardCut index))
          (instantiate (Assignment.compose candidate (schedule.nativeGuardCut index)) pattern)
          (schedule.sourceGuardInputs occurrence) := by
    rw [native_guard_input_matches, sourceGuardInputs, matches_map_iff, Assignment.instantiate_compose]
  ext physical
  constructor
  · intro member
    obtain ⟨present, checked⟩ := mem_regionOf.mp member
    change decide (physical ≠ none ∧ physical ∉ excluded ∧
      Matches schedule.guardNativeBank schedule.guardNativeFamily candidate
        (instantiate candidate (instantiate (schedule.nativeGuardCut index) pattern))
        (schedule.nativeGuardRow index (label physical).2)) = true at checked
    have accepted := of_decide_eq_true checked
    change physical ∈ insert none (before.present.image (fun occurrence => some (Sum.inl occurrence))) at present
    rcases Finset.mem_insert.mp present with control | entry
    · exact False.elim (accepted.1 control)
    · obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp entry
      refine Finset.mem_image.mpr ⟨occurrence, ?_, rfl⟩
      exact ContextualConditionalGuards.mem_region _ _ _ _ _ _ |>.mpr
        ⟨Finset.mem_filter.mpr ⟨inside, accepted.2.1⟩, (view occurrence).mp accepted.2.2⟩
  · intro member
    obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨eligible, matched⟩ := (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mp inside
    obtain ⟨present, outside⟩ := Finset.mem_filter.mp eligible
    apply mem_regionOf.mpr
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ present), ?_⟩
    change decide (some (Sum.inl occurrence) ≠ none ∧ some (Sum.inl occurrence) ∉ excluded ∧
      Matches schedule.guardNativeBank schedule.guardNativeFamily candidate
        (instantiate candidate (instantiate (schedule.nativeGuardCut index) pattern))
        (schedule.nativeGuardRow index (label (some (.inl occurrence))).2)) = true
    exact decide_eq_true ⟨Option.some_ne_none _, outside, (view occurrence).mpr matched⟩

theorem native_cut_absence_point_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat) (pattern : Term (signature S after.declarations) Γ sort)
    (excluded : Finset (GuardPhysical O)) (candidate : Assignment schedule.guardNativeFamily next) :
    ((schedule.nativeCutMatchingQuery index pattern excluded ∅).atSolution ⟨Next, next, candidate⟩).Holds
        (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
        (schedule.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Holds first (Assignment.compose candidate (schedule.nativeGuardCut index))
        schedule.sourceGuardInputs (schedule.survivingGuardInputs excluded) (.absent pattern) := by
  change regionOf _ _ ((schedule.nativeCutMatchingQuery index pattern excluded ∅).region
    ⟨Next, next, candidate⟩) = ∅ ↔ _
  erw [schedule.native_cut_query_region index occupied pattern excluded ∅ candidate, Finset.image_eq_empty]
  exact (ContextualPredicateQueryAdmission.matching_holds_iff first pattern ∅ schedule.sourceGuardInputs
    (schedule.survivingGuardInputs excluded) ⟨Next, next, Assignment.compose candidate (schedule.nativeGuardCut index)⟩).symm.trans
      (ContextualPredicateQueryAdmission.matching_empty_iff first pattern schedule.sourceGuardInputs
        (schedule.survivingGuardInputs excluded) ⟨Next, next, Assignment.compose candidate (schedule.nativeGuardCut index)⟩)

theorem native_guard_cut_model (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment schedule.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards)) :
    ContextualResidual.Models (Assignment.compose candidate (schedule.nativeGuardCut index))
      (schedule.cuts.get index).problem := by
  have global := schedule.native_binding_model_reflects occupied produced guards candidate model
  have cut := (ContextualIndependentProblems.models_iff schedule.guardVariables schedule.guardDeclarations
    schedule.guardConditions schedule.guardIndices _).mp global (.inr index)
      (schedule.guard_index_list_complete _)
  change ContextualResidual.Models
    (Assignment.compose (Assignment.compose candidate schedule.guardNativeCaptures) (schedule.guardCutInclusion index))
    (schedule.cuts.get index).problem at cut
  rw [← Assignment.compose_associative] at cut
  exact cut

/-- Native input matching does not remove countermodels of an earlier cut. -/
theorem native_guard_cut_model_extends (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate (schedule.cuts.get index).problem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment schedule.guardNativeFamily extension.declarations,
        ContextualResidual.Models combined (schedule.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose combined (schedule.nativeGuardCut index) = Assignment.compose extension.assignment candidate := by
  obtain ⟨blocks, global, guarded, cut⟩ := ContextualIndependentProblems.extend_model
    schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
    (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inr index) candidate model
  obtain ⟨ports, combined, solved, caller⟩ := schedule.native_binding_model_extends shapes resources occupied
    produced guards global guarded
  refine ⟨blocks.trans ports, combined, solved, ?_⟩
  erw [nativeGuardCut, Assignment.compose_associative, caller, ← Assignment.compose_associative,
    cut, ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
  rfl

/-- An actual-row complete query retains exactly the original-cut absence
judgment for surviving entry rows. Virtual prefix creations are separate. -/
theorem native_cut_absence_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    ContextualPredicateQueryAdmission.AskData (schedule.nativeBindingInformation occupied produced guards)
        (schedule.nativeCutMatchingQuery index pattern excluded ∅)
        (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
        (schedule.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask first (schedule.cuts.get index).problem schedule.sourceGuardInputs
        (schedule.survivingGuardInputs excluded) (.absent pattern) := by
  constructor
  · intro observed Future future candidate model
    obtain ⟨extension, native, solved, cut⟩ := schedule.native_guard_cut_model_extends index shapes resources
      consistent occupied produced guards candidate model
    have held := (schedule.native_cut_absence_point_iff index occupied pattern excluded native).mp
      (observed extension.Names extension.declarations native solved)
    rw [cut] at held
    exact (ContextualIndependentProblems.holds_extension_iff first extension candidate schedule.sourceGuardInputs
      (schedule.survivingGuardInputs excluded) (.absent pattern)).mp held
  · intro observed Future future candidate model
    exact (schedule.native_cut_absence_point_iff index occupied pattern excluded candidate).mpr
      (observed Future future _ (schedule.native_guard_cut_model index occupied produced guards candidate model))

theorem native_saved_cut_ask_iff {Local : Type} (locals : Local → MetaArity S)
    (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (rows : OccurrenceAllocationRenaming.Name O → Row locals after.declarations Γ sort)
    (world : Finset (OccurrenceAllocationRenaming.Name O))
    (check : Check (Term (signature S after.declarations) Γ sort)) :
    ContextualConditionalGuards.Ask locals (schedule.nativeBindingInformation occupied produced guards)
        (fun physical => (rows physical).map locals after.declarations (schedule.nativeGuardCut index)) world
        (check.map (instantiate (schedule.nativeGuardCut index))) ↔
      ContextualConditionalGuards.Ask locals (schedule.cuts.get index).problem rows world check := by
  constructor
  · intro observed Future future candidate model
    obtain ⟨extension, native, solved, cut⟩ := schedule.native_guard_cut_model_extends index shapes resources
      consistent occupied produced guards candidate model
    have held := (ContextualConditionalGuards.holds_transport locals (schedule.nativeGuardCut index) native rows world check).mp
      (observed extension.Names extension.declarations native solved)
    rw [cut] at held
    exact (ContextualIndependentProblems.holds_extension_iff locals extension candidate rows world check).mp held
  · intro observed Future future candidate model
    exact (ContextualConditionalGuards.holds_transport locals (schedule.nativeGuardCut index) candidate rows world check).mpr
      (observed Future future _ (schedule.native_guard_cut_model index occupied produced guards candidate model))

/-- Source prefix absence splits into surviving actual inputs and the finite
authored creations. The latter must not disappear during entry regression. -/
theorem entry_cut_absence_point_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Holds (schedule.entryCutAt index).view.locals candidate
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.absent pattern) ↔
      ContextualConditionalGuards.Holds first candidate schedule.sourceGuardInputs
          (schedule.survivingGuardInputs ((schedule.entryCutAt index).taken.image some)) (.absent pattern) ∧
        ContextualConditionalGuards.Holds (schedule.entryCutAt index).view.locals candidate
          (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).made (.absent pattern) := by
  classical
  let cut := schedule.entryCutAt index
  have member : cut ∈ schedule.entryCuts := List.get_mem _ _
  have outside (occurrence : O) : some (Sum.inl occurrence) ∉ cut.taken.image some ↔ Sum.inl occurrence ∉ cut.taken := by
    simp only [Finset.mem_image, Option.some.injEq, exists_eq_right]
  have oldWorld : before.present.image Sum.inl \ cut.taken =
      (schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl := by
    ext physical
    constructor
    · intro present
      obtain ⟨initial, untouched⟩ := Finset.mem_sdiff.mp present
      obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp initial
      exact Finset.mem_image.mpr ⟨occurrence, Finset.mem_filter.mpr ⟨inside, (outside occurrence).mpr untouched⟩, rfl⟩
    · intro present
      obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp present
      obtain ⟨initial, untouched⟩ := Finset.mem_filter.mp inside
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ initial, (outside occurrence).mp untouched⟩
  have initial := ContextualGuardRegression.holds_image_of_matches first cut.view.locals Sum.inl
    (fun _ _ same => Sum.inl.inj same) candidate schedule.sourceGuardInputs cut.view.rows
    (schedule.survivingGuardInputs (cut.taken.image some))
    (fun observed occurrence _present => by
      rw [sourceGuardInputs, matches_map_iff]
      exact (schedule.entry_cut_inputs cut member Next next candidate (instantiate candidate observed) occurrence).symm)
    (.absent pattern)
  change ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows cut.view.world (.absent pattern) ↔ _
  rw [schedule.entry_cut_world cut member, oldWorld]
  have split :
      ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows
          ((schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl ∪ cut.made) (.absent pattern) ↔
        ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows
            ((schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl) (.absent pattern) ∧
          ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows cut.made (.absent pattern) := by
    simp only [ContextualConditionalGuards.Holds, Finset.mem_union, or_imp, forall_and]
  exact split.trans (and_congr initial Iff.rfl)

theorem entry_cut_absence_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.absent pattern) ↔
      ContextualConditionalGuards.Ask first (schedule.cuts.get index).problem schedule.sourceGuardInputs
          (schedule.survivingGuardInputs ((schedule.entryCutAt index).taken.image some)) (.absent pattern) ∧
        ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.cuts.get index).problem
          (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).made (.absent pattern) := by
  rw [(schedule.entry_cut_at_compare shapes resources index).1]
  constructor
  · intro observed
    exact ⟨fun Future future candidate model => (schedule.entry_cut_absence_point_iff index candidate pattern).mp
        (observed Future future candidate model) |>.1,
      fun Future future candidate model => (schedule.entry_cut_absence_point_iff index candidate pattern).mp
        (observed Future future candidate model) |>.2⟩
  · rintro ⟨initial, created⟩ Future future candidate model
    exact (schedule.entry_cut_absence_point_iff index candidate pattern).mpr
      ⟨initial Future future candidate model, created Future future candidate model⟩

noncomputable def nativeVirtualAbsenceQuery (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualPredicateQueryAdmission.DataQuery schedule.guardNativeFamily
      (GuardPhysical O × Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O) :=
  ContextualPredicateQueryAdmission.liftPoint (ContextualPredicateQueryAdmission.ofCondition
    (fun candidate => ContextualConditionalGuards.Holds (schedule.entryCutAt index).view.locals candidate.assignment
      (fun physical => ((schedule.entryCutAt index).view.rows physical).map (schedule.entryCutAt index).view.locals
        after.declarations (schedule.nativeGuardCut index)) (schedule.entryCutAt index).made
      (.absent (instantiate (schedule.nativeGuardCut index) pattern))) none)

theorem native_virtual_absence_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualPredicateQueryAdmission.AskData (schedule.nativeBindingInformation occupied produced guards)
        (schedule.nativeVirtualAbsenceQuery index pattern)
        (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
        (schedule.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.cuts.get index).problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).made (.absent pattern) := by
  erw [nativeVirtualAbsenceQuery, ContextualPredicateQueryAdmission.lift_point_ask_iff]
  erw [ContextualPredicateQueryAdmission.ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
  exact schedule.native_saved_cut_ask_iff (schedule.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).made (.absent pattern)

/-- The complete regressed absence condition uses real input data and a
separate finite check of the prefix's authored creations at the same cut. -/
theorem native_entry_absence_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.absent pattern) ↔
      ContextualPredicateQueryAdmission.AskData (schedule.nativeBindingInformation occupied produced guards)
          (schedule.nativeCutMatchingQuery index pattern ((schedule.entryCutAt index).taken.image some) ∅)
          (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present ∧
        ContextualPredicateQueryAdmission.AskData (schedule.nativeBindingInformation occupied produced guards)
          (schedule.nativeVirtualAbsenceQuery index pattern)
          (ContextualPredicateQueryAdmission.nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present :=
  (schedule.entry_cut_absence_iff index shapes resources pattern).trans
    (and_congr (schedule.native_cut_absence_iff index shapes resources consistent occupied produced guards pattern
      ((schedule.entryCutAt index).taken.image some)).symm
      (schedule.native_virtual_absence_iff index shapes resources consistent occupied produced guards pattern).symm)

/-- Equality uses the native step's existing guard form. Its saved-cut
terms are interpreted under the same actual binding information. -/
theorem native_entry_equal_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (left right : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.equal left right) ↔
      ContextualConditionalGuards.Ask schedule.guardNativeBank (schedule.nativeBindingInformation occupied produced guards)
        (ContextualConditionalExecution.guardRows schedule.guardNativeBank schedule.guardFamily
          (schedule.nativeBindingState occupied).rows) (schedule.nativeBindingState occupied).present
        (.equal (instantiate (schedule.nativeGuardCut index) left) (instantiate (schedule.nativeGuardCut index) right)) := by
  rw [(schedule.entry_cut_at_compare shapes resources index).1]
  exact (schedule.native_saved_cut_ask_iff (schedule.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world
    (.equal left right)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
