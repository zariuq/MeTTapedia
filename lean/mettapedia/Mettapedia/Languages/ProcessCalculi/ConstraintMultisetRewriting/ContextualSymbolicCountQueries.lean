import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SymbolicPredicateTable
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardViews

/-!
# Conditional count tables at the actual native information cut

The fixed support table contains row data, not a fixed set of successful
matches. Each future model selects its own matching subset. A predicate
query validates that behavior against actual supplied input labels.
No completed principal update is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalGuards
open ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

noncomputable def nativeCountPredicate (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O))
    (candidate : Candidate schedule.guardNativeFamily) (physical : GuardPhysical O)
    (row : Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) : Bool :=
  (schedule.nativeCutMatchingQuery index pattern excluded ∅).region candidate (physical, row)

def nativeCountLabels (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (physical : GuardPhysical O) : Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort :=
  (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied) physical).2

noncomputable def nativeCountTable (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    SymbolicPredicateTable.Table (Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O) :=
  SymbolicPredicateTable.snapshot (schedule.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (schedule.nativeBindingInformation occupied produced guards))
    (schedule.nativeCountLabels occupied) (schedule.nativeBindingState occupied).present

/-- The symbolic table is constructed before the count verdict. Every
actual information model validates the same support with its own matches. -/
theorem native_count_table_read (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    AskData (schedule.nativeBindingInformation occupied produced guards)
      ((schedule.nativeCountTable index occupied produced guards pattern excluded).query
        (schedule.nativeCountPredicate index pattern excluded))
      (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
      (schedule.nativeBindingState occupied).present := by
  intro Future future candidate model
  exact SymbolicPredicateTable.snapshot_admitted (schedule.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (schedule.nativeBindingInformation occupied produced guards))
    (schedule.nativeCountLabels occupied) (schedule.nativeBindingState occupied).present
    ⟨Future, future, candidate⟩ model

theorem native_count_table_matching (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O))
    (candidate : Assignment schedule.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards)) :
    (schedule.nativeCountTable index occupied produced guards pattern excluded).matching
        (schedule.nativeCountPredicate index pattern excluded) ⟨Next, next, candidate⟩ =
      regionOf (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
        (schedule.nativeBindingState occupied).present
        ((schedule.nativeCutMatchingQuery index pattern excluded ∅).region ⟨Next, next, candidate⟩) :=
  SymbolicPredicateTable.snapshot_matching (schedule.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (schedule.nativeBindingInformation occupied produced guards))
    (schedule.nativeCountLabels occupied) (schedule.nativeBindingState occupied).present
    ⟨Next, next, candidate⟩ model

private theorem old_guard_world (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    before.present.image Sum.inl \ (schedule.entryCutAt index).taken =
      (schedule.survivingGuardInputs ((schedule.entryCutAt index).taken.image some)).image Sum.inl := by
  classical
  ext physical
  have outside (occurrence : O) :
      some (Sum.inl occurrence) ∉ (schedule.entryCutAt index).taken.image some ↔
        Sum.inl occurrence ∉ (schedule.entryCutAt index).taken := by
    simp only [Finset.mem_image, Option.some.injEq, exists_eq_right]
  constructor
  · intro member
    obtain ⟨present, untouched⟩ := Finset.mem_sdiff.mp member
    obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp present
    exact Finset.mem_image.mpr ⟨occurrence, Finset.mem_filter.mpr ⟨inside, (outside occurrence).mpr untouched⟩, rfl⟩
  · intro member
    obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨present, untouched⟩ := Finset.mem_filter.mp inside
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ present, (outside occurrence).mp untouched⟩

/-- The prefix count is a sum over disjoint surviving-input and creation
identities. Private row conditions remain in each matching predicate. -/
theorem entry_cut_count (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S after.declarations) Γ sort) :
    (region (schedule.entryCutAt index).view.locals candidate (schedule.entryCutAt index).view.rows
        (schedule.entryCutAt index).view.world pattern).card =
      (region first candidate schedule.sourceGuardInputs
        (schedule.survivingGuardInputs ((schedule.entryCutAt index).taken.image some)) pattern).card +
        (region (schedule.entryCutAt index).view.locals candidate (schedule.entryCutAt index).view.rows
          (schedule.entryCutAt index).made pattern).card := by
  classical
  let cut := schedule.entryCutAt index
  have member : cut ∈ schedule.entryCuts := List.get_mem _ _
  have inputRegion := ContextualGuardRegression.region_image_of_matches first cut.view.locals Sum.inl
    candidate schedule.sourceGuardInputs cut.view.rows
    (schedule.survivingGuardInputs (cut.taken.image some)) pattern
    (fun occurrence _present => by
      rw [sourceGuardInputs, matches_map_iff]
      exact (schedule.entry_cut_inputs cut member Next next candidate (instantiate candidate pattern) occurrence).symm)
  have apart : Disjoint
      (region cut.view.locals candidate cut.view.rows
        ((schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl) pattern)
      (region cut.view.locals candidate cut.view.rows cut.made pattern) := by
    apply Finset.disjoint_left.mpr
    intro physical old new
    obtain ⟨occurrence, _present, rfl⟩ := Finset.mem_image.mp ((mem_region _ _ _ _ _ _).mp old).1
    exact schedule.entry_cut_created_not_initial cut member occurrence ((mem_region _ _ _ _ _ _).mp new).1
  change (region cut.view.locals candidate cut.view.rows cut.view.world pattern).card = _
  rw [schedule.entry_cut_world cut member, old_guard_world]
  have unionRegion :
      region cut.view.locals candidate cut.view.rows
          (((schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl) ∪ cut.made) pattern =
        region cut.view.locals candidate cut.view.rows
            ((schedule.survivingGuardInputs (cut.taken.image some)).image Sum.inl) pattern ∪
          region cut.view.locals candidate cut.view.rows cut.made pattern := by
    simp only [region, Finset.filter_union]
  rw [unionRegion, Finset.card_union_of_disjoint apart, inputRegion,
    Finset.card_image_of_injective _ (fun _ _ same => Sum.inl.inj same)]

noncomputable def nativeVirtualCount (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) (candidate : Candidate schedule.guardNativeFamily) : Nat :=
  (region (schedule.entryCutAt index).view.locals candidate.assignment
    (fun physical => ((schedule.entryCutAt index).view.rows physical).map (schedule.entryCutAt index).view.locals
      after.declarations (schedule.nativeGuardCut index))
    (schedule.entryCutAt index).made (instantiate (schedule.nativeGuardCut index) pattern)).card

theorem native_count_total (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (candidate : Assignment schedule.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards)) :
    (region (schedule.entryCutAt index).view.locals (Assignment.compose candidate (schedule.nativeGuardCut index))
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world pattern).card =
      ((schedule.nativeCountTable index occupied produced guards pattern ((schedule.entryCutAt index).taken.image some)).matching
        (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)) ⟨Next, next, candidate⟩).card +
        schedule.nativeVirtualCount index pattern ⟨Next, next, candidate⟩ := by
  rw [schedule.entry_cut_count index (Assignment.compose candidate (schedule.nativeGuardCut index)) pattern,
    schedule.native_count_table_matching index occupied produced guards pattern _ candidate model,
    schedule.native_cut_query_region index occupied pattern _ ∅ candidate,
    Finset.card_image_of_injective _ (fun _ _ same => Sum.inl.inj (Option.some.inj same))]
  congr 1
  exact (congrArg Finset.card (ContextualConditionalGuards.region_transport
    (schedule.entryCutAt index).view.locals (schedule.nativeGuardCut index) candidate
    (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).made pattern)).symm

theorem native_count_total_of_read (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O))
    (candidate : Assignment schedule.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards))
    (read : ((table.query (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some))).atSolution
      ⟨Next, next, candidate⟩).Holds (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
      (schedule.nativeBindingState occupied).present) :
    (region (schedule.entryCutAt index).view.locals (Assignment.compose candidate (schedule.nativeGuardCut index))
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world pattern).card =
      (table.matching (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some))
        ⟨Next, next, candidate⟩).card + schedule.nativeVirtualCount index pattern ⟨Next, next, candidate⟩ := by
  have observed := table.actual_region (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some))
    ⟨Next, next, candidate⟩ (schedule.nativeCountLabels occupied) (schedule.nativeBindingState occupied).present read
  have reconstructed := (schedule.native_count_table_matching index occupied produced guards pattern
    ((schedule.entryCutAt index).taken.image some) candidate model).trans observed
  rw [schedule.native_count_total index occupied produced guards pattern candidate model, reconstructed]

noncomputable def nativeCountCheckQuery (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O))
    (number : Nat) :
    DataQuery schedule.guardNativeFamily
      (GuardPhysical O × Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O) :=
  liftPoint (ofCondition (fun candidate =>
    (table.matching
      (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)) candidate).card +
      schedule.nativeVirtualCount index pattern candidate = number) none)

/-- Any table whose actual-data read succeeds may supply the finite count
check. The table need not have been constructed from this inventory. -/
theorem native_entry_count_from_table_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O))
    (number : Nat)
    (read : AskData (schedule.nativeBindingInformation occupied produced guards)
      (table.query (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)))
      (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present) :
    Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.count pattern number) ↔
        AskData (schedule.nativeBindingInformation occupied produced guards)
          (schedule.nativeCountCheckQuery index pattern table number)
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present := by
  have point :
      AskData (schedule.nativeBindingInformation occupied produced guards)
          (schedule.nativeCountCheckQuery index pattern table number)
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present ↔
        ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment schedule.guardNativeFamily future),
          ContextualResidual.Models candidate (schedule.nativeBindingInformation occupied produced guards) →
          (table.matching
            (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)) ⟨Future, future, candidate⟩).card +
            schedule.nativeVirtualCount index pattern ⟨Future, future, candidate⟩ = number := by
    erw [nativeCountCheckQuery, lift_point_ask_iff]
    exact ask_condition_iff _ _ _ (Finset.mem_insert_self _ _) _
  have semantic := schedule.native_saved_cut_ask_iff (schedule.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.count pattern number)
  rw [(schedule.entry_cut_at_compare shapes resources index).1]
  constructor
  · intro source
    apply point.mpr
    intro Future future candidate model
    have holds := semantic.mpr source Future future candidate model
    have original := (ContextualConditionalGuards.holds_transport (schedule.entryCutAt index).view.locals
      (schedule.nativeGuardCut index) candidate (schedule.entryCutAt index).view.rows
      (schedule.entryCutAt index).view.world (.count pattern number)).mp holds
    change (region _ _ _ _ pattern).card = number at original
    rwa [schedule.native_count_total_of_read index occupied produced guards pattern table candidate model
      (read Future future candidate model)] at original
  · intro checked
    apply semantic.mp
    intro Future future candidate model
    apply (ContextualConditionalGuards.holds_transport (schedule.entryCutAt index).view.locals
      (schedule.nativeGuardCut index) candidate (schedule.entryCutAt index).view.rows
      (schedule.entryCutAt index).view.world (.count pattern number)).mpr
    change (region _ _ _ _ pattern).card = number
    rw [schedule.native_count_total_of_read index occupied produced guards pattern table candidate model
      (read Future future candidate model)]
    exact point.mp checked Future future candidate model

/-- The constructed symbolic table read and its finite count check give
the exact original guard, including with residual/nonprincipal information. -/
theorem native_entry_count_iff (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (number : Nat) :
    let table := schedule.nativeCountTable index occupied produced guards pattern ((schedule.entryCutAt index).taken.image some)
    Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.count pattern number) ↔
      AskData (schedule.nativeBindingInformation occupied produced guards)
          (table.query (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)))
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present ∧
        AskData (schedule.nativeBindingInformation occupied produced guards)
          (schedule.nativeCountCheckQuery index pattern table number)
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present := by
  dsimp only
  constructor
  · intro source
    have read := schedule.native_count_table_read index occupied produced guards pattern
      ((schedule.entryCutAt index).taken.image some)
    exact ⟨read, (schedule.native_entry_count_from_table_iff index shapes resources consistent occupied produced guards pattern
      _ number read).mp source⟩
  · rintro ⟨read, checked⟩
    exact (schedule.native_entry_count_from_table_iff index shapes resources consistent occupied produced guards pattern
      _ number read).mpr checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
