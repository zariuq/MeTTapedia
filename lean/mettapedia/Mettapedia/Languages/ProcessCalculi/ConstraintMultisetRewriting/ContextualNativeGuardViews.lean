import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission

/-!
# Actual native row labels interpreted at an original guard cut

The current caller and each saved guard cut have distinct declaration
blocks. Resetting the captures of an actual row to a saved block recovers
the original input's meaning at that cut. Schema-private names stay private.
Queries apply this reset to the row supplied by the current inventory;
they do not consult a captured source row dictionary.
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

def guardCutInclusion (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment after.declarations body.guardFamily :=
  ContextualIndependentProblems.inclusion body.guardVariables body.guardDeclarations (.inr index)

def guardCutReset (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment body.guardFamily body.guardFamily := fun name =>
  match name with
  | ⟨.inl none, name⟩ => generator body.guardFamily ⟨.inr index, name⟩
  | ⟨.inl (some birth), name⟩ => generator body.guardFamily ⟨.inl (some birth), name⟩
  | ⟨.inr cut, name⟩ => generator body.guardFamily ⟨.inr cut, name⟩

theorem guard_cut_reset_current (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment.compose (body.guardCutReset index) body.bindingCurrent = body.guardCutInclusion index := by
  funext name
  exact instantiate_generator _ _

theorem guard_cut_reset_captures (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment.compose (body.guardCutReset index) body.bindingCaptures =
      Assignment.compose (body.guardCutInclusion index) body.frame.assignment := by
  rw [ContextualNativeBodies.Body.bindingCaptures, Assignment.compose_associative, guard_cut_reset_current]

abbrev guardNativeBank (body : Body S O Γ sort before after) :=
  ContextualClauseFrames.bank body.bindingLocals body.bindingLocals

abbrev guardNativeFamily (body : Body S O Γ sort before after) :=
  ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily

abbrev guardNativeCaptures (body : Body S O Γ sort before after) :
    Assignment body.guardFamily body.guardNativeFamily :=
  ContextualSelectionViews.capturedTarget body.guardNativeBank body.guardFamily

def nativeGuardReset (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment body.guardNativeFamily body.guardNativeFamily
  | .inl name => generator body.guardNativeFamily (.inl name)
  | .inr name => instantiate body.guardNativeCaptures (body.guardCutReset index name)

theorem native_guard_reset_captures (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment.compose (body.nativeGuardReset index) body.guardNativeCaptures =
      Assignment.compose body.guardNativeCaptures (body.guardCutReset index) := by
  funext name
  exact instantiate_generator _ _

def nativeGuardCut (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment after.declarations body.guardNativeFamily :=
  Assignment.compose body.guardNativeCaptures (body.guardCutInclusion index)

theorem native_guard_reset_root (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Assignment.compose (body.nativeGuardReset index)
        (Assignment.compose body.guardNativeCaptures body.bindingCaptures) =
      Assignment.compose (body.nativeGuardCut index) body.frame.assignment := by
  rw [Assignment.compose_associative, native_guard_reset_captures,
    ← Assignment.compose_associative, guard_cut_reset_captures, Assignment.compose_associative]
  rfl

def nativeGuardRow (body : Body S O Γ sort before after) (index : body.CutIndex)
    (row : Row body.guardNativeBank body.guardNativeFamily Γ sort) :
    Row body.guardNativeBank body.guardNativeFamily Γ sort :=
  row.map body.guardNativeBank body.guardNativeFamily (body.nativeGuardReset index)

/-- Resetting an actual prepared input label recovers its original caller
at the selected saved cut, including the row's latent private conditions. -/
theorem native_guard_input_matches (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat) (occurrence : O) (candidate : Assignment body.guardNativeFamily next)
    (pattern : Term (signature S next) Γ sort) :
    Matches body.guardNativeBank body.guardNativeFamily candidate pattern
      (body.nativeGuardRow index
        (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank
          (body.nativeBindingState occupied) (some (.inl occurrence))).2) ↔
      Matches first before.declarations
        (Assignment.compose (Assignment.compose candidate (body.nativeGuardCut index)) body.frame.assignment)
        pattern (before.rows occurrence) := by
  change Matches _ _ candidate pattern
    (((ContextualConditionalExecution.guardRows body.guardNativeBank body.guardFamily
        (body.nativeBindingState occupied).rows (some (.inl occurrence))).map
      body.guardNativeBank body.guardNativeFamily (body.nativeGuardReset index))) ↔ _
  rw [matches_map_iff]
  change Matches _ _ (Assignment.compose candidate (body.nativeGuardReset index)) pattern
    ((ContextualConditionalPublication.extendPrivate body.bindingLocals body.bindingLocals body.guardFamily
      (body.bindingInput occurrence)).map body.guardNativeBank body.guardFamily body.guardNativeCaptures) ↔ _
  rw [matches_map_iff, ContextualConditionalPublication.extendPrivate_matches_iff,
    ContextualNativeBodies.Body.binding_input_matches]
  have square :
      Assignment.compose
          (Assignment.compose (Assignment.compose candidate (body.nativeGuardReset index)) body.guardNativeCaptures)
          body.bindingCaptures =
        Assignment.compose (Assignment.compose candidate (body.nativeGuardCut index)) body.frame.assignment := by
    rw [← Assignment.compose_associative, ← Assignment.compose_associative,
      native_guard_reset_root, Assignment.compose_associative]
  rw [square]

noncomputable def nativeCutMatchingQuery (body : Body S O Γ sort before after) (index : body.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort)
    (excluded seen : Finset (GuardPhysical O)) :
    ContextualPredicateQueryAdmission.DataQuery body.guardNativeFamily
      (GuardPhysical O × Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O) := by
  classical
  exact ⟨(fun candidate label => decide (label.1 ≠ none ∧ label.1 ∉ excluded ∧
    Matches body.guardNativeBank body.guardNativeFamily candidate.assignment
      (instantiate candidate.assignment (instantiate (body.nativeGuardCut index) pattern))
      (body.nativeGuardRow index label.2))), seen⟩

def survivingGuardInputs (_body : Body S O Γ sort before after)
    (excluded : Finset (GuardPhysical O)) : Finset O :=
  before.present.filter fun occurrence => some (.inl occurrence) ∉ excluded

def sourceGuardInputs (body : Body S O Γ sort before after) : O → Row first after.declarations Γ sort :=
  fun occurrence => (before.rows occurrence).map first before.declarations body.frame.assignment

/-- The real query region is exactly the surviving entry matching region
at the saved cut. The program/control occurrence contributes no match. -/
theorem native_cut_query_region (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat) (pattern : Term (signature S after.declarations) Γ sort)
    (excluded seen : Finset (GuardPhysical O)) (candidate : Assignment body.guardNativeFamily next) :
    regionOf (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
        (body.nativeBindingState occupied).present
        ((body.nativeCutMatchingQuery index pattern excluded seen).region ⟨Next, next, candidate⟩) =
      (ContextualConditionalGuards.region first (Assignment.compose candidate (body.nativeGuardCut index))
        body.sourceGuardInputs (body.survivingGuardInputs excluded) pattern).image
        (fun occurrence => some (Sum.inl occurrence)) := by
  classical
  let label := ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied)
  have view (occurrence : O) :
      Matches body.guardNativeBank body.guardNativeFamily candidate
          (instantiate candidate (instantiate (body.nativeGuardCut index) pattern))
          (body.nativeGuardRow index (label (some (.inl occurrence))).2) ↔
        Matches first after.declarations (Assignment.compose candidate (body.nativeGuardCut index))
          (instantiate (Assignment.compose candidate (body.nativeGuardCut index)) pattern)
          (body.sourceGuardInputs occurrence) := by
    rw [native_guard_input_matches, sourceGuardInputs, matches_map_iff, Assignment.instantiate_compose]
  ext physical
  constructor
  · intro member
    obtain ⟨present, checked⟩ := mem_regionOf.mp member
    change decide (physical ≠ none ∧ physical ∉ excluded ∧
      Matches body.guardNativeBank body.guardNativeFamily candidate
        (instantiate candidate (instantiate (body.nativeGuardCut index) pattern))
        (body.nativeGuardRow index (label physical).2)) = true at checked
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
      Matches body.guardNativeBank body.guardNativeFamily candidate
        (instantiate candidate (instantiate (body.nativeGuardCut index) pattern))
        (body.nativeGuardRow index (label (some (.inl occurrence))).2)) = true
    exact decide_eq_true ⟨Option.some_ne_none _, outside, (view occurrence).mpr matched⟩

theorem native_cut_absence_point_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat) (pattern : Term (signature S after.declarations) Γ sort)
    (excluded : Finset (GuardPhysical O)) (candidate : Assignment body.guardNativeFamily next) :
    ((body.nativeCutMatchingQuery index pattern excluded ∅).atSolution ⟨Next, next, candidate⟩).Holds
        (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
        (body.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Holds first (Assignment.compose candidate (body.nativeGuardCut index))
        body.sourceGuardInputs (body.survivingGuardInputs excluded) (.absent pattern) := by
  change regionOf _ _ ((body.nativeCutMatchingQuery index pattern excluded ∅).region
    ⟨Next, next, candidate⟩) = ∅ ↔ _
  erw [body.native_cut_query_region index occupied pattern excluded ∅ candidate, Finset.image_eq_empty]
  exact (ContextualPredicateQueryAdmission.matching_holds_iff first pattern ∅ body.sourceGuardInputs
    (body.survivingGuardInputs excluded) ⟨Next, next, Assignment.compose candidate (body.nativeGuardCut index)⟩).symm.trans
      (ContextualPredicateQueryAdmission.matching_empty_iff first pattern body.sourceGuardInputs
        (body.survivingGuardInputs excluded) ⟨Next, next, Assignment.compose candidate (body.nativeGuardCut index)⟩)

theorem native_guard_cut_model (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment body.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards)) :
    ContextualResidual.Models (Assignment.compose candidate (body.nativeGuardCut index))
      (body.cuts.get index).problem := by
  have global := body.native_binding_model_reflects occupied produced guards candidate model
  have cut := (ContextualIndependentProblems.models_iff body.guardVariables body.guardDeclarations
    body.guardConditions body.guardIndices _).mp global (.inr index)
      (body.guard_index_cut_listed index)
  change ContextualResidual.Models
    (Assignment.compose (Assignment.compose candidate body.guardNativeCaptures) (body.guardCutInclusion index))
    (body.cuts.get index).problem at cut
  rw [← Assignment.compose_associative] at cut
  exact cut

/-- Native input matching does not remove countermodels of an earlier cut. -/
theorem native_guard_cut_model_extends (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate (body.cuts.get index).problem) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment body.guardNativeFamily extension.declarations,
        ContextualResidual.Models combined (body.nativeBindingInformation occupied produced guards) ∧
          Assignment.compose combined (body.nativeGuardCut index) = Assignment.compose extension.assignment candidate := by
  obtain ⟨blocks, global, guarded, cut⟩ := ContextualIndependentProblems.extend_model
    body.guardVariables body.guardDeclarations body.guardConditions
    (body.guard_blocks_solvable consistent) body.guardIndices (.inr index) candidate model
  obtain ⟨ports, combined, solved, caller⟩ := body.native_binding_model_extends shapes resources occupied
    produced guards global guarded
  refine ⟨blocks.trans ports, combined, solved, ?_⟩
  erw [nativeGuardCut, Assignment.compose_associative, caller, ← Assignment.compose_associative,
    cut, ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
  rfl

/-- An actual-row complete query retains exactly the original-cut absence
judgment for surviving entry rows. Virtual prefix creations are separate. -/
theorem native_cut_absence_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation occupied produced guards)
        (body.nativeCutMatchingQuery index pattern excluded ∅)
        (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
        (body.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask first (body.cuts.get index).problem body.sourceGuardInputs
        (body.survivingGuardInputs excluded) (.absent pattern) := by
  constructor
  · intro observed Future future candidate model
    obtain ⟨extension, native, solved, cut⟩ := body.native_guard_cut_model_extends index shapes resources
      consistent occupied produced guards candidate model
    have held := (body.native_cut_absence_point_iff index occupied pattern excluded native).mp
      (observed extension.Names extension.declarations native solved)
    rw [cut] at held
    exact (ContextualIndependentProblems.holds_extension_iff first extension candidate body.sourceGuardInputs
      (body.survivingGuardInputs excluded) (.absent pattern)).mp held
  · intro observed Future future candidate model
    exact (body.native_cut_absence_point_iff index occupied pattern excluded candidate).mpr
      (observed Future future _ (body.native_guard_cut_model index occupied produced guards candidate model))

theorem native_saved_cut_ask_iff {Local : Type} (locals : Local → MetaArity S)
    (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (rows : OccurrenceAllocationRenaming.Name O → Row locals after.declarations Γ sort)
    (world : Finset (OccurrenceAllocationRenaming.Name O))
    (check : Check (Term (signature S after.declarations) Γ sort)) :
    ContextualConditionalGuards.Ask locals (body.nativeBindingInformation occupied produced guards)
        (fun physical => (rows physical).map locals after.declarations (body.nativeGuardCut index)) world
        (check.map (instantiate (body.nativeGuardCut index))) ↔
      ContextualConditionalGuards.Ask locals (body.cuts.get index).problem rows world check := by
  constructor
  · intro observed Future future candidate model
    obtain ⟨extension, native, solved, cut⟩ := body.native_guard_cut_model_extends index shapes resources
      consistent occupied produced guards candidate model
    have held := (ContextualConditionalGuards.holds_transport locals (body.nativeGuardCut index) native rows world check).mp
      (observed extension.Names extension.declarations native solved)
    rw [cut] at held
    exact (ContextualIndependentProblems.holds_extension_iff locals extension candidate rows world check).mp held
  · intro observed Future future candidate model
    exact (ContextualConditionalGuards.holds_transport locals (body.nativeGuardCut index) candidate rows world check).mpr
      (observed Future future _ (body.native_guard_cut_model index occupied produced guards candidate model))

/-- Source prefix absence splits into surviving actual inputs and the finite
authored creations. The latter must not disappear during entry regression. -/
theorem entry_cut_absence_point_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Holds (body.entryCutAt index).view.locals candidate
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.absent pattern) ↔
      ContextualConditionalGuards.Holds first candidate body.sourceGuardInputs
          (body.survivingGuardInputs ((body.entryCutAt index).taken.image some)) (.absent pattern) ∧
        ContextualConditionalGuards.Holds (body.entryCutAt index).view.locals candidate
          (body.entryCutAt index).view.rows (body.entryCutAt index).made (.absent pattern) := by
  classical
  let cut := body.entryCutAt index
  have member : cut ∈ body.entryCuts := List.get_mem _ _
  have outside (occurrence : O) : some (Sum.inl occurrence) ∉ cut.taken.image some ↔ Sum.inl occurrence ∉ cut.taken := by
    simp only [Finset.mem_image, Option.some.injEq, exists_eq_right]
  have oldWorld : before.present.image Sum.inl \ cut.taken =
      (body.survivingGuardInputs (cut.taken.image some)).image Sum.inl := by
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
    (fun _ _ same => Sum.inl.inj same) candidate body.sourceGuardInputs cut.view.rows
    (body.survivingGuardInputs (cut.taken.image some))
    (fun observed occurrence _present => by
      rw [sourceGuardInputs, matches_map_iff]
      exact (body.entry_cut_inputs cut member Next next candidate (instantiate candidate observed) occurrence).symm)
    (.absent pattern)
  change ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows cut.view.world (.absent pattern) ↔ _
  rw [body.entry_cut_world cut member, oldWorld]
  have split :
      ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows
          ((body.survivingGuardInputs (cut.taken.image some)).image Sum.inl ∪ cut.made) (.absent pattern) ↔
        ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows
            ((body.survivingGuardInputs (cut.taken.image some)).image Sum.inl) (.absent pattern) ∧
          ContextualConditionalGuards.Holds cut.view.locals candidate cut.view.rows cut.made (.absent pattern) := by
    simp only [ContextualConditionalGuards.Holds, Finset.mem_union, or_imp, forall_and]
  exact split.trans (and_congr initial Iff.rfl)

theorem entry_cut_absence_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.absent pattern) ↔
      ContextualConditionalGuards.Ask first (body.cuts.get index).problem body.sourceGuardInputs
          (body.survivingGuardInputs ((body.entryCutAt index).taken.image some)) (.absent pattern) ∧
        ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.cuts.get index).problem
          (body.entryCutAt index).view.rows (body.entryCutAt index).made (.absent pattern) := by
  rw [(body.entry_cut_at_compare shapes resources index).1]
  constructor
  · intro observed
    exact ⟨fun Future future candidate model => (body.entry_cut_absence_point_iff index candidate pattern).mp
        (observed Future future candidate model) |>.1,
      fun Future future candidate model => (body.entry_cut_absence_point_iff index candidate pattern).mp
        (observed Future future candidate model) |>.2⟩
  · rintro ⟨initial, created⟩ Future future candidate model
    exact (body.entry_cut_absence_point_iff index candidate pattern).mpr
      ⟨initial Future future candidate model, created Future future candidate model⟩

noncomputable def nativeVirtualAbsenceQuery (body : Body S O Γ sort before after) (index : body.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualPredicateQueryAdmission.DataQuery body.guardNativeFamily
      (GuardPhysical O × Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O) :=
  ContextualPredicateQueryAdmission.liftPoint (ContextualPredicateQueryAdmission.ofCondition
    (fun candidate => ContextualConditionalGuards.Holds (body.entryCutAt index).view.locals candidate.assignment
      (fun physical => ((body.entryCutAt index).view.rows physical).map (body.entryCutAt index).view.locals
        after.declarations (body.nativeGuardCut index)) (body.entryCutAt index).made
      (.absent (instantiate (body.nativeGuardCut index) pattern))) none)

theorem native_virtual_absence_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation occupied produced guards)
        (body.nativeVirtualAbsenceQuery index pattern)
        (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
        (body.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.cuts.get index).problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).made (.absent pattern) := by
  erw [nativeVirtualAbsenceQuery, ContextualPredicateQueryAdmission.lift_point_ask_iff]
  erw [ContextualPredicateQueryAdmission.ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
  exact body.native_saved_cut_ask_iff (body.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (body.entryCutAt index).view.rows (body.entryCutAt index).made (.absent pattern)

/-- The complete regressed absence condition uses real input data and a
separate finite check of the prefix's authored creations at the same cut. -/
theorem native_entry_absence_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.absent pattern) ↔
      ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation occupied produced guards)
          (body.nativeCutMatchingQuery index pattern ((body.entryCutAt index).taken.image some) ∅)
          (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present ∧
        ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation occupied produced guards)
          (body.nativeVirtualAbsenceQuery index pattern)
          (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present :=
  (body.entry_cut_absence_iff index shapes resources pattern).trans
    (and_congr (body.native_cut_absence_iff index shapes resources consistent occupied produced guards pattern
      ((body.entryCutAt index).taken.image some)).symm
      (body.native_virtual_absence_iff index shapes resources consistent occupied produced guards pattern).symm)

/-- Equality uses the native step's existing guard form. Its saved-cut
terms are interpreted under the same actual binding information. -/
theorem native_entry_equal_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (left right : Term (signature S after.declarations) Γ sort) :
    ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.equal left right) ↔
      ContextualConditionalGuards.Ask body.guardNativeBank (body.nativeBindingInformation occupied produced guards)
        (ContextualConditionalExecution.guardRows body.guardNativeBank body.guardFamily
          (body.nativeBindingState occupied).rows) (body.nativeBindingState occupied).present
        (.equal (instantiate (body.nativeGuardCut index) left) (instantiate (body.nativeGuardCut index) right)) := by
  rw [(body.entry_cut_at_compare shapes resources index).1]
  exact (body.native_saved_cut_ask_iff (body.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (body.entryCutAt index).view.rows (body.entryCutAt index).view.world
    (.equal left right)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
