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

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

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

noncomputable def nativeCountPredicate (body : Body S O Γ sort before after) (index : body.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O))
    (candidate : Candidate body.guardNativeFamily) (physical : GuardPhysical O)
    (row : Row body.guardNativeBank body.guardNativeFamily Γ sort) : Bool :=
  (body.nativeCutMatchingQuery index pattern excluded ∅).region candidate (physical, row)

def nativeCountLabels (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (physical : GuardPhysical O) : Row body.guardNativeBank body.guardNativeFamily Γ sort :=
  (nativeLabels body.guardNativeBank (body.nativeBindingState occupied) physical).2

noncomputable def nativeCountTable (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    SymbolicPredicateTable.Table (Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O) :=
  SymbolicPredicateTable.snapshot (body.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (body.nativeBindingInformation occupied produced guards))
    (body.nativeCountLabels occupied) (body.nativeBindingState occupied).present

/-- The symbolic table is constructed before the count verdict. Every
actual information model validates the same support with its own matches. -/
theorem native_count_table_read (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O)) :
    AskData (body.nativeBindingInformation occupied produced guards)
      ((body.nativeCountTable index occupied produced guards pattern excluded).query
        (body.nativeCountPredicate index pattern excluded))
      (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
      (body.nativeBindingState occupied).present := by
  intro Future future candidate model
  exact SymbolicPredicateTable.snapshot_admitted (body.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (body.nativeBindingInformation occupied produced guards))
    (body.nativeCountLabels occupied) (body.nativeBindingState occupied).present
    ⟨Future, future, candidate⟩ model

theorem native_count_table_matching (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (excluded : Finset (GuardPhysical O))
    (candidate : Assignment body.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards)) :
    (body.nativeCountTable index occupied produced guards pattern excluded).matching
        (body.nativeCountPredicate index pattern excluded) ⟨Next, next, candidate⟩ =
      regionOf (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
        (body.nativeBindingState occupied).present
        ((body.nativeCutMatchingQuery index pattern excluded ∅).region ⟨Next, next, candidate⟩) :=
  SymbolicPredicateTable.snapshot_matching (body.nativeCountPredicate index pattern excluded)
    (fun candidate => ContextualResidual.Models candidate.assignment
      (body.nativeBindingInformation occupied produced guards))
    (body.nativeCountLabels occupied) (body.nativeBindingState occupied).present
    ⟨Next, next, candidate⟩ model

private theorem old_guard_world (body : Body S O Γ sort before after) (index : body.CutIndex) :
    before.present.image Sum.inl \ (body.entryCutAt index).taken =
      (body.survivingGuardInputs ((body.entryCutAt index).taken.image some)).image Sum.inl := by
  classical
  ext physical
  have outside (occurrence : O) :
      some (Sum.inl occurrence) ∉ (body.entryCutAt index).taken.image some ↔
        Sum.inl occurrence ∉ (body.entryCutAt index).taken := by
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
theorem entry_cut_count (body : Body S O Γ sort before after) (index : body.CutIndex)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S after.declarations) Γ sort) :
    (region (body.entryCutAt index).view.locals candidate (body.entryCutAt index).view.rows
        (body.entryCutAt index).view.world pattern).card =
      (region first candidate body.sourceGuardInputs
        (body.survivingGuardInputs ((body.entryCutAt index).taken.image some)) pattern).card +
        (region (body.entryCutAt index).view.locals candidate (body.entryCutAt index).view.rows
          (body.entryCutAt index).made pattern).card := by
  classical
  let cut := body.entryCutAt index
  have member : cut ∈ body.entryCuts := List.get_mem _ _
  have inputRegion := ContextualGuardRegression.region_image_of_matches first cut.view.locals Sum.inl
    candidate body.sourceGuardInputs cut.view.rows
    (body.survivingGuardInputs (cut.taken.image some)) pattern
    (fun occurrence _present => by
      rw [sourceGuardInputs, matches_map_iff]
      exact (body.entry_cut_inputs cut member Next next candidate (instantiate candidate pattern) occurrence).symm)
  have apart : Disjoint
      (region cut.view.locals candidate cut.view.rows
        ((body.survivingGuardInputs (cut.taken.image some)).image Sum.inl) pattern)
      (region cut.view.locals candidate cut.view.rows cut.made pattern) := by
    apply Finset.disjoint_left.mpr
    intro physical old new
    obtain ⟨occurrence, _present, rfl⟩ := Finset.mem_image.mp ((mem_region _ _ _ _ _ _).mp old).1
    exact body.entry_cut_created_not_initial cut member occurrence ((mem_region _ _ _ _ _ _).mp new).1
  change (region cut.view.locals candidate cut.view.rows cut.view.world pattern).card = _
  rw [body.entry_cut_world cut member, old_guard_world]
  have unionRegion :
      region cut.view.locals candidate cut.view.rows
          (((body.survivingGuardInputs (cut.taken.image some)).image Sum.inl) ∪ cut.made) pattern =
        region cut.view.locals candidate cut.view.rows
            ((body.survivingGuardInputs (cut.taken.image some)).image Sum.inl) pattern ∪
          region cut.view.locals candidate cut.view.rows cut.made pattern := by
    simp only [region, Finset.filter_union]
  rw [unionRegion, Finset.card_union_of_disjoint apart, inputRegion,
    Finset.card_image_of_injective _ (fun _ _ same => Sum.inl.inj same)]

noncomputable def nativeVirtualCount (body : Body S O Γ sort before after) (index : body.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort) (candidate : Candidate body.guardNativeFamily) : Nat :=
  (region (body.entryCutAt index).view.locals candidate.assignment
    (fun physical => ((body.entryCutAt index).view.rows physical).map (body.entryCutAt index).view.locals
      after.declarations (body.nativeGuardCut index))
    (body.entryCutAt index).made (instantiate (body.nativeGuardCut index) pattern)).card

theorem native_count_total (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (candidate : Assignment body.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards)) :
    (region (body.entryCutAt index).view.locals (Assignment.compose candidate (body.nativeGuardCut index))
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world pattern).card =
      ((body.nativeCountTable index occupied produced guards pattern ((body.entryCutAt index).taken.image some)).matching
        (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)) ⟨Next, next, candidate⟩).card +
        body.nativeVirtualCount index pattern ⟨Next, next, candidate⟩ := by
  rw [body.entry_cut_count index (Assignment.compose candidate (body.nativeGuardCut index)) pattern,
    body.native_count_table_matching index occupied produced guards pattern _ candidate model,
    body.native_cut_query_region index occupied pattern _ ∅ candidate,
    Finset.card_image_of_injective _ (fun _ _ same => Sum.inl.inj (Option.some.inj same))]
  congr 1
  exact (congrArg Finset.card (ContextualConditionalGuards.region_transport
    (body.entryCutAt index).view.locals (body.nativeGuardCut index) candidate
    (body.entryCutAt index).view.rows (body.entryCutAt index).made pattern)).symm

theorem native_count_total_of_read (body : Body S O Γ sort before after) (index : body.CutIndex)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O))
    (candidate : Assignment body.guardNativeFamily next)
    (model : ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards))
    (read : ((table.query (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some))).atSolution
      ⟨Next, next, candidate⟩).Holds (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
      (body.nativeBindingState occupied).present) :
    (region (body.entryCutAt index).view.locals (Assignment.compose candidate (body.nativeGuardCut index))
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world pattern).card =
      (table.matching (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some))
        ⟨Next, next, candidate⟩).card + body.nativeVirtualCount index pattern ⟨Next, next, candidate⟩ := by
  have observed := table.actual_region (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some))
    ⟨Next, next, candidate⟩ (body.nativeCountLabels occupied) (body.nativeBindingState occupied).present read
  have reconstructed := (body.native_count_table_matching index occupied produced guards pattern
    ((body.entryCutAt index).taken.image some) candidate model).trans observed
  rw [body.native_count_total index occupied produced guards pattern candidate model, reconstructed]

noncomputable def nativeCountCheckQuery (body : Body S O Γ sort before after) (index : body.CutIndex)
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O))
    (number : Nat) :
    DataQuery body.guardNativeFamily
      (GuardPhysical O × Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O) :=
  liftPoint (ofCondition (fun candidate =>
    (table.matching
      (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)) candidate).card +
      body.nativeVirtualCount index pattern candidate = number) none)

/-- Any table whose actual-data read succeeds may supply the finite count
check. The table need not have been constructed from this inventory. -/
theorem native_entry_count_from_table_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort)
    (table : SymbolicPredicateTable.Table (Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O))
    (number : Nat)
    (read : AskData (body.nativeBindingInformation occupied produced guards)
      (table.query (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)))
      (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present) :
    Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.count pattern number) ↔
        AskData (body.nativeBindingInformation occupied produced guards)
          (body.nativeCountCheckQuery index pattern table number)
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present := by
  have point :
      AskData (body.nativeBindingInformation occupied produced guards)
          (body.nativeCountCheckQuery index pattern table number)
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present ↔
        ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment body.guardNativeFamily future),
          ContextualResidual.Models candidate (body.nativeBindingInformation occupied produced guards) →
          (table.matching
            (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)) ⟨Future, future, candidate⟩).card +
            body.nativeVirtualCount index pattern ⟨Future, future, candidate⟩ = number := by
    erw [nativeCountCheckQuery, lift_point_ask_iff]
    exact ask_condition_iff _ _ _ (Finset.mem_insert_self _ _) _
  have semantic := body.native_saved_cut_ask_iff (body.entryCutAt index).view.locals index shapes resources consistent
    occupied produced guards (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.count pattern number)
  rw [(body.entry_cut_at_compare shapes resources index).1]
  constructor
  · intro source
    apply point.mpr
    intro Future future candidate model
    have holds := semantic.mpr source Future future candidate model
    have original := (ContextualConditionalGuards.holds_transport (body.entryCutAt index).view.locals
      (body.nativeGuardCut index) candidate (body.entryCutAt index).view.rows
      (body.entryCutAt index).view.world (.count pattern number)).mp holds
    change (region _ _ _ _ pattern).card = number at original
    rwa [body.native_count_total_of_read index occupied produced guards pattern table candidate model
      (read Future future candidate model)] at original
  · intro checked
    apply semantic.mp
    intro Future future candidate model
    apply (ContextualConditionalGuards.holds_transport (body.entryCutAt index).view.locals
      (body.nativeGuardCut index) candidate (body.entryCutAt index).view.rows
      (body.entryCutAt index).view.world (.count pattern number)).mpr
    change (region _ _ _ _ pattern).card = number
    rw [body.native_count_total_of_read index occupied produced guards pattern table candidate model
      (read Future future candidate model)]
    exact point.mp checked Future future candidate model

/-- The constructed symbolic table read and its finite count check give
the exact original guard, including with residual/nonprincipal information. -/
theorem native_entry_count_iff (body : Body S O Γ sort before after) (index : body.CutIndex)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (pattern : Term (signature S after.declarations) Γ sort) (number : Nat) :
    let table := body.nativeCountTable index occupied produced guards pattern ((body.entryCutAt index).taken.image some)
    Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.count pattern number) ↔
      AskData (body.nativeBindingInformation occupied produced guards)
          (table.query (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)))
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present ∧
        AskData (body.nativeBindingInformation occupied produced guards)
          (body.nativeCountCheckQuery index pattern table number)
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present := by
  dsimp only
  constructor
  · intro source
    have read := body.native_count_table_read index occupied produced guards pattern
      ((body.entryCutAt index).taken.image some)
    exact ⟨read, (body.native_entry_count_from_table_iff index shapes resources consistent occupied produced guards pattern
      _ number read).mp source⟩
  · rintro ⟨read, checked⟩
    exact (body.native_entry_count_from_table_iff index shapes resources consistent occupied produced guards pattern
      _ number read).mpr checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
