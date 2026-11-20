import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordLayouts

/-! Exact information and admission of the constrained-information queue
profile. Source witnesses satisfy the actual accumulated knowledge; the
permission function remains fixed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe u v w

attribute [local irreducible] NativeClauseData.signature

theorem matching_satisfies_at {Value : Type v} {old locals later : Frame.{u}}
    (patterns : List (Terms Value locals)) (selected : List Occurrence)
    (rows : Occurrence → Terms Value old) (opening : Hom locals later) (weakening : Hom old later)
    (environment : later.Carrier) :
    Satisfies (patterns.zipWith (fun pattern occurrence =>
      (pattern ∘ opening, rows occurrence ∘ weakening)) selected) environment ↔
      PreparedRules.Matches patterns selected (fun occurrence => rows occurrence (weakening environment))
        (opening environment) := by
  induction patterns generalizing selected with
  | nil => simp [Satisfies, PreparedRules.Matches]
  | cons pattern rest ih =>
      cases selected with
      | nil => simp [Satisfies, PreparedRules.Matches]
      | cons occurrence next =>
          simpa [Satisfies, PreparedRules.Matches] using and_congr_right (fun _ => ih next)

namespace ViewData

variable {Cell : Field → Type u} {Event : Type u}
    {state : RuleSyntax.State (Terms (AtomData Cell Event)) Occurrence} {layout : Layout}
    {environment : state.frame.Carrier} {fields : (name : Field) → Cell name}
    {cursor : Nat} {pending : List Event}
    (view : ViewData state layout environment fields cursor pending)

include view in
theorem pending_slot {occurrence : Occurrence} (present : occurrence ∈ state.present)
    (otherCursor : Nat) (otherPending : List Event)
    (matched : AtomData.pending otherCursor otherPending = state.label occurrence environment) :
    occurrence = layout.request ∧ otherCursor = cursor ∧ otherPending = pending := by
  have inside : occurrence ∈ layout.support := view.exact ▸ present
  rcases Finset.mem_insert.mp inside with same | inside
  · have labelled := matched.trans ((congrArg (fun occurrence => state.label occurrence environment) same).trans view.request)
    have equal := AtomData.pending.inj labelled
    exact ⟨same, equal.1, equal.2⟩
  · obtain ⟨name, _, same⟩ := Finset.mem_image.mp inside
    have impossible := matched.trans
      ((congrArg (fun occurrence => state.label occurrence environment) same.symm).trans (view.field name))
    cases impossible

include view in
theorem field_slot {occurrence : Occurrence} (present : occurrence ∈ state.present)
    (name : Field) (value : Cell name)
    (matched : AtomData.field name value = state.label occurrence environment) :
    occurrence = layout.field name := by
  have inside : occurrence ∈ layout.support := view.exact ▸ present
  rcases Finset.mem_insert.mp inside with same | inside
  · have impossible := matched.trans
      ((congrArg (fun occurrence => state.label occurrence environment) same).trans view.request)
    cases impossible
  · obtain ⟨other, _, same⟩ := Finset.mem_image.mp inside
    have labelled := matched.trans
      ((congrArg (fun occurrence => state.label occurrence environment) same.symm).trans (view.field other))
    have sameName := (AtomData.field.inj labelled).1
    exact same.symm.trans (congrArg layout.field sameName.symm)

end ViewData

theorem atom_field_injective {Cell : Field → Type u} {Event : Type u} (name : Field) :
    Function.Injective (AtomData.field (Cell := Cell) (Event := Event) name) := by
  intro first second same
  exact eq_of_heq (AtomData.field.inj same).2

def selectionFor (writes : List Field) (generation : Field → Nat) (cursor : Nat) : Selection Occurrence where
  taken := .request cursor :: writes.map (row generation)
  read := (Field.all.filter (fun field => field ∉ writes)).map (row generation)
  made := .request (cursor+1) :: writes.map (nextRow generation)

def selectionAt (layout : Layout) (writes : List Field) (made : List Occurrence) : Selection Occurrence where
  taken := layout.request :: writes.map layout.field
  read := (Field.all.filter (fun name => name ∉ writes)).map layout.field
  made := made

theorem selectionAt_enabled (layout : Layout) (writes : List Field) (made : List Occurrence)
    (fresh : Disjoint made.toFinset layout.support) :
    Enabled (fun _ : Occurrence => ()) layout.support ((selectionAt layout writes made).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, fresh, ?_⟩
  · intro occurrence member
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with rfl | member
    · exact Finset.mem_insert_self _ _
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
      exact NativeRecordLayouts.field_mem_support layout name
  · intro occurrence member
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact NativeRecordLayouts.field_mem_support layout name
  · apply Finset.disjoint_left.mpr
    intro occurrence taken read
    obtain ⟨name, readMember, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp read)
    rcases List.mem_cons.mp (List.mem_toFinset.mp taken) with same | taken
    · exact layout.request_not_field name same.symm
    · obtain ⟨other, written, equal⟩ := List.mem_map.mp taken
      have same := layout.field_injective equal
      have missing : name ∉ writes := by simpa using (List.mem_filter.mp readMember).2
      exact missing (same ▸ written)
  · intro query member
    cases member

def generationAfter (writes : List Field) (generation : Field → Nat) (field : Field) : Nat :=
  if field ∈ writes then generation field + 1 else generation field

theorem mem_support_field (generation : Field → Nat) (cursor : Nat) (field : Field) (serial : Nat) :
    Occurrence.field field serial ∈ (canonicalLayout generation cursor).support ↔ serial = generation field := by
  constructor
  · intro inside
    rcases Finset.mem_insert.mp inside with impossible | inside
    · cases impossible
    · obtain ⟨other, _, same⟩ := Finset.mem_image.mp inside
      have equal := Occurrence.field.inj same
      rcases equal with ⟨rfl, equal⟩
      exact equal.symm
  · intro same
    subst serial
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨field,
      List.mem_toFinset.mpr (NativeFieldExecution.field_member field), rfl⟩

theorem mem_support_request (generation : Field → Nat) (cursor serial : Nat) :
    Occurrence.request serial ∈ (canonicalLayout generation cursor).support ↔ serial = cursor := by
  constructor
  · intro inside
    rcases Finset.mem_insert.mp inside with same | inside
    · exact Occurrence.request.inj same
    · obtain ⟨field, _, same⟩ := Finset.mem_image.mp inside
      cases same
  · rintro rfl
    exact Finset.mem_insert_self _ _

theorem selectionFor_field_taken (writes : List Field) (generation : Field → Nat) (cursor : Nat)
    (field : Field) (serial : Nat) :
    Occurrence.field field serial ∈ (selectionFor writes generation cursor).taken.toFinset ↔
      field ∈ writes ∧ serial = generation field := by
  simp [selectionFor, row, eq_comm, and_left_comm]

theorem selectionFor_field_made (writes : List Field) (generation : Field → Nat) (cursor : Nat)
    (field : Field) (serial : Nat) :
    Occurrence.field field serial ∈ (selectionFor writes generation cursor).made.toFinset ↔
      field ∈ writes ∧ serial = generation field + 1 := by
  simp [selectionFor, nextRow, eq_comm, and_left_comm]

theorem selectionFor_request_taken (writes : List Field) (generation : Field → Nat) (cursor serial : Nat) :
    Occurrence.request serial ∈ (selectionFor writes generation cursor).taken.toFinset ↔ serial = cursor := by
  simp [selectionFor, row]

theorem selectionFor_request_made (writes : List Field) (generation : Field → Nat) (cursor serial : Nat) :
    Occurrence.request serial ∈ (selectionFor writes generation cursor).made.toFinset ↔ serial = cursor + 1 := by
  simp [selectionFor, nextRow]

theorem canonical_present_after (writes : List Field) (generation : Field → Nat) (cursor : Nat) :
    MeTTaCalculus.OccurrenceCommits.fire (canonicalLayout generation cursor).support
      ((selectionFor writes generation cursor).commit (T := Unit)) =
      (canonicalLayout (generationAfter writes generation) (cursor+1)).support := by
  apply Finset.ext
  intro occurrence
  simp only [MeTTaCalculus.OccurrenceCommits.fire, Finset.mem_union, Finset.mem_sdiff]
  change ((occurrence ∈ (canonicalLayout generation cursor).support ∧
      occurrence ∉ (selectionFor writes generation cursor).taken.toFinset) ∨
    occurrence ∈ (selectionFor writes generation cursor).made.toFinset) ↔ _
  cases occurrence with
  | request serial =>
      simp only [mem_support_request, selectionFor_request_taken, selectionFor_request_made,
        and_not_self, false_or]
  | field field serial =>
      simp only [mem_support_field, selectionFor_field_taken, selectionFor_field_made]
      by_cases written : field ∈ writes
      · simp [generationAfter, written]
      · simp [generationAfter, written]

namespace QueueClause

variable {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    (clause : QueueClause Cell Record Effect)
    {rules : RuleSyntax.Program (Terms (AtomData Cell (Record × Effect.Carrier)))}
    (member : clause.rule ∈ rules)

def firing {old : Frame.{u}} (selected : Selection Occurrence) :
    RuleSyntax.Firing Occurrence extensions rules old := canonical clause.rule member selected

/-- Every actual opening and selection of this rule has this form. No
canonical-opening restriction is imposed on the inversion results. -/
def firingAt {old : Frame.{u}} (extension : Frame.{u})
    (opening : Hom clause.localFrame (extend old extension)) (selected : Selection Occurrence)
    (seen : List (Finset Occurrence)) : RuleSyntax.Firing Occurrence extensions rules old :=
  ⟨clause.rule, member, extension, opening, selected, seen⟩

theorem information_at_iff
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (extension : Frame.{u}) (opening : Hom clause.localFrame (extend state.frame extension))
    (selected : Selection Occurrence) (seen : List (Finset Occurrence))
    (environment : (extend state.frame extension).Carrier) :
    Satisfies ((clause.firingAt member extension opening selected seen).information
      (frames (AtomData Cell (Record × Effect.Carrier))) state) environment ↔
      Satisfies state.knowledge environment.1 ∧
      PreparedRules.Matches clause.rule.body.take selected.taken
        (fun occurrence => state.label occurrence environment.1) (opening environment) ∧
      PreparedRules.Matches clause.rule.body.read selected.read
        (fun occurrence => state.label occurrence environment.1) (opening environment) ∧
      clause.guard (opening environment).values (opening environment).effect := by
  simp only [RuleSyntax.Firing.information, RuleSyntax.Firing.matching, RuleSyntax.Firing.row,
    firingAt, RuleSyntax.Firing.opened, RuleInstance.map, Frames.applyStore, frames, extensions,
    List.zipWith_map_left]
  rw [PreparedRules.satisfies_append, PreparedRules.satisfies_append,
    PreparedRules.satisfies_append, PreparedRules.satisfies_reindexed]
  rw [matching_satisfies_at, matching_satisfies_at]
  simp [Satisfies, rule, guardTerm, truthTerm, and_assoc]

omit member in
theorem matched_field_positions
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (names : List Field) (selected : List Occurrence) (lengths : names.length = selected.length)
    (present : ∀ occurrence ∈ selected, occurrence ∈ state.present)
    (matched : PreparedRules.Matches (names.map clause.beforeTerm) selected
      (fun occurrence => state.label occurrence environment) locals) :
    selected = names.map layout.field := by
  induction names generalizing selected with
  | nil => exact List.length_eq_zero_iff.mp lengths.symm
  | cons name rest ih =>
      cases selected with
      | nil => simp at lengths
      | cons occurrence tail =>
          have firstMatch := matched (clause.beforeTerm name, occurrence) List.mem_cons_self
          have firstPosition := view.field_slot (present occurrence List.mem_cons_self) name
            (clause.before name locals.values) firstMatch
          have tailMatch : PreparedRules.Matches (rest.map clause.beforeTerm) tail
              (fun occurrence => state.label occurrence environment) locals :=
            fun pair inside => matched pair (List.mem_cons_of_mem _ inside)
          have later := ih tail (Nat.succ.inj lengths)
            (fun next inside => present next (List.mem_cons_of_mem _ inside)) tailMatch
          exact congrArg₂ List.cons firstPosition later

omit member in
theorem matches_fields_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values) (names : List Field) :
    PreparedRules.Matches (names.map clause.beforeTerm) (names.map layout.field)
      (fun occurrence => state.label occurrence environment) locals := by
  unfold PreparedRules.Matches
  rw [List.zip_map']
  intro pair inside
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp inside
  exact (congrArg (AtomData.field name) (same name).symm).trans (view.field name).symm

omit member in
theorem matches_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values) (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail) (made : List Occurrence) :
    PreparedRules.Matches clause.rule.body.take (selectionAt layout clause.writes made).taken
        (fun occurrence => state.label occurrence environment) locals ∧
      PreparedRules.Matches clause.rule.body.read (selectionAt layout clause.writes made).read
        (fun occurrence => state.label occurrence environment) locals := by
  constructor
  · change PreparedRules.Matches (clause.pendingTerm :: clause.writes.map clause.beforeTerm)
      (layout.request :: clause.writes.map layout.field) (fun occurrence => state.label occurrence environment) locals
    unfold PreparedRules.Matches
    rw [List.zip_cons_cons, List.forall_mem_cons]
    constructor
    · exact (congrArg₂ (AtomData.pending (Cell := Cell)) sameCursor samePending.symm).trans view.request.symm
    · exact clause.matches_fields_at_view state layout environment fields cursor pending view locals same _
  · exact clause.matches_fields_at_view state layout environment fields cursor pending view locals same _

structure InputData
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat)
    (pending : List (Record × Effect.Carrier)) (locals : clause.localFrame.Carrier)
    (selected : Selection Occurrence) : Prop where
  taken : selected.taken = layout.request :: clause.writes.map layout.field
  read : selected.read = (Field.all.filter (fun name => name ∉ clause.writes)).map layout.field
  cursorSame : locals.cursor = cursor
  pendingSame : pending = (clause.record locals.values, locals.effect) :: locals.tail
  fieldsSame : ∀ name, fields name = clause.before name locals.values

omit member in
theorem input_inversion
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (selected : Selection Occurrence)
    (takeLength : clause.rule.body.take.length = selected.taken.length)
    (readLength : clause.rule.body.read.length = selected.read.length)
    (enabled : Enabled (fun _ : Occurrence => ()) state.present (selected.commit (T := Unit)))
    (takes : PreparedRules.Matches clause.rule.body.take selected.taken
      (fun occurrence => state.label occurrence environment) locals)
    (reads : PreparedRules.Matches clause.rule.body.read selected.read
      (fun occurrence => state.label occurrence environment) locals) :
    clause.InputData state layout fields cursor pending locals selected := by
  have takeData : selected.taken = layout.request :: clause.writes.map layout.field ∧
      locals.cursor = cursor ∧ pending = (clause.record locals.values, locals.effect) :: locals.tail := by
    cases chosen : selected.taken with
    | nil => simp [rule, chosen] at takeLength
    | cons occurrence tail =>
        have firstPresent : occurrence ∈ state.present := enabled.taken_subset
          (List.mem_toFinset.mpr (by rw [chosen]; exact List.mem_cons_self))
        have firstMatch : clause.pendingTerm locals = state.label occurrence environment :=
          takes (clause.pendingTerm, occurrence) (by rw [chosen]; exact List.mem_cons_self)
        have firstPosition := view.pending_slot firstPresent locals.cursor
          ((clause.record locals.values, locals.effect) :: locals.tail) firstMatch
        have tailLength : clause.writes.length = tail.length := Nat.succ.inj
          (by simpa only [rule, chosen, List.length_cons, List.length_map] using takeLength)
        have tailMatch : PreparedRules.Matches (clause.writes.map clause.beforeTerm) tail
            (fun occurrence => state.label occurrence environment) locals := by
          intro pair inside
          exact takes pair (by rw [chosen]; exact List.mem_cons_of_mem _ inside)
        have tailPositions := clause.matched_field_positions state layout environment fields cursor pending view locals
          clause.writes tail tailLength
          (fun next inside => enabled.taken_subset (List.mem_toFinset.mpr
            (by rw [chosen]; exact List.mem_cons_of_mem _ inside))) tailMatch
        exact ⟨congrArg₂ List.cons firstPosition.1 tailPositions,
          firstPosition.2.1, firstPosition.2.2.symm⟩
  have readPositions := clause.matched_field_positions state layout environment fields cursor pending view locals
    (Field.all.filter (fun name => name ∉ clause.writes)) selected.read
    (by simpa only [rule, List.length_map] using readLength)
    (fun occurrence inside => enabled.kept_subset (List.mem_toFinset.mpr inside)) reads
  refine ⟨takeData.1, readPositions, takeData.2.1, takeData.2.2, ?_⟩
  intro name
  have matched : clause.beforeTerm name locals = state.label (layout.field name) environment := by
    by_cases written : name ∈ clause.writes
    · apply takes (clause.beforeTerm name, layout.field name)
      rw [takeData.1]
      apply List.mem_cons_of_mem
      change (clause.beforeTerm name, layout.field name) ∈
        (clause.writes.map clause.beforeTerm).zip (clause.writes.map layout.field)
      rw [List.zip_map']
      exact List.mem_map.mpr ⟨name, written, rfl⟩
    · have inside : name ∈ Field.all.filter (fun field => field ∉ clause.writes) :=
        List.mem_filter.mpr ⟨NativeFieldExecution.field_member name, by simpa using written⟩
      apply reads (clause.beforeTerm name, layout.field name)
      rw [readPositions]
      change (clause.beforeTerm name, layout.field name) ∈
        ((Field.all.filter (fun field => field ∉ clause.writes)).map clause.beforeTerm).zip
          ((Field.all.filter (fun field => field ∉ clause.writes)).map layout.field)
      rw [List.zip_map']
      exact List.mem_map.mpr ⟨name, inside, rfl⟩
  exact (atom_field_injective name (matched.trans (view.field name))).symm

theorem result_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (extension : Frame.{u}) (opening : Hom clause.localFrame (extend state.frame extension))
    (selected : Selection Occurrence) (seen : List (Finset Occurrence))
    (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions rules).Admits
      (s := state) (clause.firingAt member extension opening selected seen))
    (environment : (extend state.frame extension).Carrier)
    (satisfies : Satisfies ((clause.firingAt member extension opening selected seen).result
      (frames (AtomData Cell (Record × Effect.Carrier))) state).knowledge environment)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat)
    (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment.1 fields cursor pending)
    (input : clause.InputData state layout fields cursor pending (opening environment) selected)
    (replacement : NativeRecordLayouts.Replacement layout clause.writes selected.made) :
    ViewData ((clause.firingAt member extension opening selected seen).result
      (frames (AtomData Cell (Record × Effect.Carrier))) state) replacement.next environment
      (fun name => clause.after name (opening environment).values) (cursor+1) (opening environment).tail := by
  let active := clause.firingAt member extension opening selected seen
  let after := active.result (frames (AtomData Cell (Record × Effect.Carrier))) state
  have reordered : selected.made.zip (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce =
      (replacement.next.request :: clause.writes.map replacement.next.field).zip
        (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce :=
    congrArg (fun made : List Occurrence => made.zip
      (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce) replacement.made_eq
  refine ⟨?_, satisfies, ?_, ?_⟩
  · change (state.present \ selected.taken.toFinset) ∪ selected.made.toFinset = replacement.next.support
    calc
      _ = (layout.support \ NativeRecordLayouts.taken layout clause.writes) ∪ selected.made.toFinset := by
        rw [view.exact, input.taken]
        rfl
      _ = _ := replacement.exact_support.symm
  · intro name
    by_cases written : name ∈ clause.writes
    · have made : (replacement.next.field name,
          fun values : (extend state.frame extension).Carrier => clause.afterTerm name (opening values)) ∈
          selected.made.zip (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce := by
        apply Eq.mpr (congrArg (fun rows => (replacement.next.field name,
          fun values : (extend state.frame extension).Carrier => clause.afterTerm name (opening values)) ∈ rows) reordered)
        apply List.mem_cons_of_mem
        change (replacement.next.field name,
          fun values : (extend state.frame extension).Carrier => clause.afterTerm name (opening values)) ∈
          (clause.writes.map replacement.next.field).zip
            ((clause.writes.map clause.afterTerm).map
              (fun term (values : (extend state.frame extension).Carrier) => term (opening values)))
        rw [List.map_map, List.zip_map']
        exact List.mem_map.mpr ⟨name, written, rfl⟩
      exact congrFun (RuleSyntax.Firing.result_label_made active admitted.1 made) environment
    · have oldPresent : layout.field name ∈ state.present :=
        view.exact.symm ▸ NativeRecordLayouts.field_mem_support layout name
      have missing : layout.field name ∉ selected.made := by
        intro made
        exact (Finset.disjoint_left.mp admitted.2.1.fresh) (List.mem_toFinset.mpr made) oldPresent
      have labelled := congrFun (RuleSyntax.Firing.result_label_other
        (X := frames (AtomData Cell (Record × Effect.Carrier))) active missing) environment
      exact (congrArg (fun occurrence => after.label occurrence environment)
        (replacement.unwritten name written)).trans
        (labelled.trans ((view.field name).trans
          ((congrArg (AtomData.field name) (input.fieldsSame name)).trans
            (congrArg (AtomData.field name) (clause.unchanged name written (opening environment).values).symm))))
  · have made : (replacement.next.request,
        fun values : (extend state.frame extension).Carrier => clause.residualTerm (opening values)) ∈
        selected.made.zip (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce := by
      apply Eq.mpr (congrArg (fun rows => (replacement.next.request,
        fun values : (extend state.frame extension).Carrier => clause.residualTerm (opening values)) ∈ rows) reordered)
      exact List.mem_cons_self
    have labelled := congrFun (RuleSyntax.Firing.result_label_made active admitted.1 made) environment
    exact labelled.trans (congrArg (fun serial => AtomData.pending serial (opening environment).tail)
      (congrArg (fun serial => serial+1) input.cursorSame))

structure InversionAtData
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (extension : Frame.{u}) (opening : Hom clause.localFrame (extend state.frame extension))
    (selected : Selection Occurrence) (seen : List (Finset Occurrence))
    (environment : (extend state.frame extension).Carrier) (layout : Layout)
    (fields : (name : Field) → Cell name) (cursor : Nat) (pending : List (Record × Effect.Carrier)) where
  input : clause.InputData state layout fields cursor pending (opening environment) selected
  valid : clause.guard (opening environment).values (opening environment).effect
  replacement : NativeRecordLayouts.Replacement layout clause.writes selected.made
  result : ViewData ((clause.firingAt member extension opening selected seen).result
      (frames (AtomData Cell (Record × Effect.Carrier))) state) replacement.next environment
    (fun name => clause.after name (opening environment).values) (cursor+1) (opening environment).tail

/-- Inversion of one actual firing at any exact current layout and any
satisfying result point. Replacement uses its actual ordered made list. -/
def invert_at
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (extension : Frame.{u}) (opening : Hom clause.localFrame (extend state.frame extension))
    (selected : Selection Occurrence) (seen : List (Finset Occurrence))
    (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions rules).Admits
      (s := state) (clause.firingAt member extension opening selected seen))
    (environment : (extend state.frame extension).Carrier)
    (satisfies : Satisfies ((clause.firingAt member extension opening selected seen).result
      (frames (AtomData Cell (Record × Effect.Carrier))) state).knowledge environment)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat)
    (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment.1 fields cursor pending) :
    clause.InversionAtData member state extension opening selected seen environment layout fields cursor pending := by
  have information := (clause.information_at_iff member state extension opening selected seen environment).mp satisfies
  have input := clause.input_inversion state layout environment.1 fields cursor pending view (opening environment)
    selected admitted.1.2.2.2.1 admitted.1.2.2.2.2.1 admitted.2.1 information.2.1 information.2.2.1
  have length : selected.made.length = 1 + clause.writes.length := by
    have shaped := admitted.1.2.2.2.2.2.1
    simpa only [firingAt, rule, List.length_cons, List.length_map, Nat.add_comm] using shaped.symm
  have fresh : Disjoint selected.made.toFinset layout.support := view.exact ▸ admitted.2.1.fresh
  let replacement := NativeRecordLayouts.replace layout clause.writes selected.made length
    admitted.1.2.2.1 fresh clause.writes_distinct
  exact {
    input := input
    valid := information.2.2.2
    replacement := replacement
    result := clause.result_at_view member state extension opening selected seen admitted environment satisfies
      layout fields cursor pending view input replacement }

theorem information_iff
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (selected : Selection Occurrence) (environment : (extend state.frame clause.localFrame).Carrier) :
    Satisfies ((clause.firing member (old := state.frame) selected).information
      (frames (AtomData Cell (Record × Effect.Carrier))) state) environment ↔
      Satisfies state.knowledge environment.1 ∧
      PreparedRules.Matches clause.rule.body.take selected.taken
        (fun occurrence => state.label occurrence environment.1) environment.2 ∧
      PreparedRules.Matches clause.rule.body.read selected.read
        (fun occurrence => state.label occurrence environment.1) environment.2 ∧
      clause.guard environment.2.values environment.2.effect := by
  simp only [RuleSyntax.Firing.information, RuleSyntax.Firing.matching, RuleSyntax.Firing.row,
    firing, canonical, RuleSyntax.Firing.opened, RuleInstance.map, Frames.applyStore, frames, extensions,
    List.zipWith_map_left]
  rw [PreparedRules.satisfies_append, PreparedRules.satisfies_append,
    PreparedRules.satisfies_append, PreparedRules.satisfies_reindexed]
  simp only [Function.comp_def]
  rw [PreparedRules.matching_satisfies, PreparedRules.matching_satisfies]
  simp [Satisfies, rule, guardTerm, truthTerm, and_assoc]

theorem holds_iff
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (selected : Selection Occurrence) {later : Frame.{u}}
    (substitution : Hom (extend state.frame clause.localFrame) later) :
    (clause.firing member (old := state.frame) selected).Holds
      (frames (AtomData Cell (Record × Effect.Carrier))) state substitution ↔
      ∀ environment, clause.guard (substitution environment).2.values (substitution environment).2.effect := by
  change ((∀ check ∈ [Check.equal
    (fun environment => AtomData.proposition
      (clause.guard environment.2.values environment.2.effect))
    (fun _ => AtomData.proposition True)],
      RuleSyntax.checkHolds (frames (AtomData Cell (Record × Effect.Carrier))) substitution _ state.present check) ∧
      ∀ query ∈ ([] : List (Terms (AtomData Cell (Record × Effect.Carrier))
        (extend state.frame clause.localFrame) × Finset Occurrence)),
        RuleSyntax.matchesAt (frames (AtomData Cell (Record × Effect.Carrier))) substitution _
          state.present query.1 = query.2) ↔ _
  simp only [List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, RuleSyntax.checkHolds]
  constructor
  · intro same environment
    have fixed : clause.guard (substitution environment).2.values (substitution environment).2.effect = True :=
      AtomData.proposition.inj (congrFun same environment)
    exact fixed.mpr trivial
  · intro valid
    funext environment
    apply congrArg AtomData.proposition
    exact propext ⟨fun _ => trivial, fun _ => valid environment⟩

theorem asks_from_information
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (selected : Selection Occurrence) :
    (frames (AtomData Cell (Record × Effect.Carrier))).Entails
      ((clause.firing member (old := state.frame) selected).information
        (frames (AtomData Cell (Record × Effect.Carrier))) state)
      (fun _ substitution => (clause.firing member (old := state.frame) selected).Holds
        (frames (AtomData Cell (Record × Effect.Carrier))) state substitution) := by
  intro later substitution modeled
  apply (clause.holds_iff member state selected substitution).mpr
  intro environment
  have satisfies := (InterpretedFrames.models_iff substitution _).mp modeled environment
  exact ((clause.information_iff member state selected (substitution environment)).mp satisfies).2.2.2

theorem information_solvable_iff
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (selected : Selection Occurrence) :
    (frames (AtomData Cell (Record × Effect.Carrier))).Solvable
      ((clause.firing member (old := state.frame) selected).information
        (frames (AtomData Cell (Record × Effect.Carrier))) state) ↔
      ∃ (old : state.frame.Carrier) (locals : clause.localFrame.Carrier),
        Satisfies state.knowledge old ∧
        PreparedRules.Matches clause.rule.body.take selected.taken
          (fun occurrence => state.label occurrence old) locals ∧
        PreparedRules.Matches clause.rule.body.read selected.read
          (fun occurrence => state.label occurrence old) locals ∧
        clause.guard locals.values locals.effect := by
  rw [InterpretedFrames.solvable_iff]
  constructor
  · rintro ⟨environment, satisfies⟩
    exact ⟨environment.1, environment.2,
      (clause.information_iff member state selected environment).mp satisfies⟩
  · rintro ⟨old, locals, satisfies⟩
    exact ⟨(old, locals), (clause.information_iff member state selected (old, locals)).mpr satisfies⟩

theorem satisfies_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values) (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail)
    (valid : clause.guard locals.values locals.effect) (made : List Occurrence) :
    Satisfies ((clause.firing member (old := state.frame) (selectionAt layout clause.writes made)).information
      (frames (AtomData Cell (Record × Effect.Carrier))) state) (environment, locals) := by
  have matched := clause.matches_at_view state layout environment fields cursor pending view locals same
    sameCursor samePending made
  exact (clause.information_iff member state _ (environment, locals)).mpr
    ⟨view.solved, matched.1, matched.2, valid⟩

theorem shapes_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (made : List Occurrence) (length : made.length = 1 + clause.writes.length)
    (distinct : made.Nodup) :
    (clause.firing member (old := state.frame) (selectionAt layout clause.writes made)).Shapes
      (frames (AtomData Cell (Record × Effect.Carrier))) state := by
  refine ⟨canonical_fresh state clause.rule member _, ?_, distinct, ?_, ?_, ?_, rfl⟩
  · change (layout.request :: clause.writes.map layout.field).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, clause.writes_distinct.map layout.field_injective⟩
    intro inside
    obtain ⟨name, _, same⟩ := List.mem_map.mp inside
    exact layout.request_not_field name same.symm
  · simp only [firing, canonical, rule, selectionAt, List.length_cons, List.length_map]
  · simp only [firing, canonical, rule, selectionAt, List.length_map]
  · change clause.rule.body.produce.length = made.length
    simpa only [rule, List.length_cons, List.length_map, Nat.add_comm] using length.symm

theorem admitted_at_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values) (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail)
    (valid : clause.guard locals.values locals.effect) (made : List Occurrence)
    (length : made.length = 1 + clause.writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset layout.support) :
    (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions rules).Admits
      (s := state) (clause.firing member (selectionAt layout clause.writes made)) := by
  have satisfied := clause.satisfies_at_view member state layout environment fields cursor pending view locals
    same sameCursor samePending valid made
  refine ⟨clause.shapes_at_view member state layout made length distinct, ?_,
    (InterpretedFrames.solvable_iff _).mpr ⟨(environment, locals), satisfied⟩,
    clause.asks_from_information member state _⟩
  change Enabled _ state.present ((selectionAt layout clause.writes made).commit (T := Unit))
  exact view.exact.symm ▸ selectionAt_enabled layout clause.writes made fresh

omit member in
theorem matches_fields_of_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (generation : Field → Nat) (cursor : Nat) (environment : state.frame.Carrier)
    (fields : (name : Field) → Cell name) (pending : List (Record × Effect.Carrier))
    (view : ViewData state (canonicalLayout generation cursor) environment fields cursor pending)
    (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values) (names : List Field) :
    PreparedRules.Matches (names.map clause.beforeTerm) (names.map (row generation))
      (fun occurrence => state.label occurrence environment) locals := by
  unfold PreparedRules.Matches
  rw [List.zip_map']
  intro pair inside
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp inside
  change AtomData.field name (clause.before name locals.values) =
    state.label (row generation name) environment
  exact (congrArg (AtomData.field name) (same name).symm).trans (view.field name).symm

omit member in
theorem matches_of_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (generation : Field → Nat) (cursor : Nat) (environment : state.frame.Carrier)
    (fields : (name : Field) → Cell name) (pending : List (Record × Effect.Carrier))
    (view : ViewData state (canonicalLayout generation cursor) environment fields cursor pending)
    (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values)
    (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail) :
    PreparedRules.Matches clause.rule.body.take (selectionFor clause.writes generation cursor).taken
        (fun occurrence => state.label occurrence environment) locals ∧
      PreparedRules.Matches clause.rule.body.read (selectionFor clause.writes generation cursor).read
        (fun occurrence => state.label occurrence environment) locals := by
  constructor
  · change PreparedRules.Matches (clause.pendingTerm :: clause.writes.map clause.beforeTerm)
      (Occurrence.request cursor :: clause.writes.map (row generation))
      (fun occurrence => state.label occurrence environment) locals
    unfold PreparedRules.Matches
    rw [List.zip_cons_cons, List.forall_mem_cons]
    constructor
    · change AtomData.pending locals.cursor
        ((clause.record locals.values, locals.effect) :: locals.tail) =
        state.label (Occurrence.request cursor) environment
      have fixed : AtomData.pending (Cell := Cell) locals.cursor
          ((clause.record locals.values, locals.effect) :: locals.tail) =
          AtomData.pending cursor pending := congrArg₂ AtomData.pending sameCursor samePending.symm
      exact fixed.trans view.request.symm
    · exact clause.matches_fields_of_view state generation cursor environment fields pending view locals same _
  · exact clause.matches_fields_of_view state generation cursor environment fields pending view locals same _

theorem satisfies_of_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (generation : Field → Nat) (cursor : Nat) (environment : state.frame.Carrier)
    (fields : (name : Field) → Cell name) (pending : List (Record × Effect.Carrier))
    (view : ViewData state (canonicalLayout generation cursor) environment fields cursor pending)
    (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values)
    (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail)
    (valid : clause.guard locals.values locals.effect) :
    Satisfies ((clause.firing member (old := state.frame)
      (selectionFor clause.writes generation cursor)).information
      (frames (AtomData Cell (Record × Effect.Carrier))) state) (environment, locals) := by
  have matched := clause.matches_of_view state generation cursor environment fields pending view locals
    same sameCursor samePending
  exact (clause.information_iff member state _ (environment, locals)).mpr
    ⟨view.solved, matched.1, matched.2, valid⟩

theorem result_view
    (state : RuleSyntax.State (Terms (AtomData Cell (Record × Effect.Carrier))) Occurrence)
    (generation : Field → Nat) (cursor : Nat)
    (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions rules).Admits
      (s := state) (clause.firing member (selectionFor clause.writes generation cursor)))
    (environment : (extend state.frame clause.localFrame).Carrier)
    (satisfies : Satisfies ((clause.firing member (old := state.frame)
      (selectionFor clause.writes generation cursor)).result
      (frames (AtomData Cell (Record × Effect.Carrier))) state).knowledge environment)
    (fields : (name : Field) → Cell name) (pending : List (Record × Effect.Carrier))
    (view : ViewData state (canonicalLayout generation cursor) environment.1 fields cursor pending) :
    ViewData ((clause.firing member (old := state.frame)
        (selectionFor clause.writes generation cursor)).result
        (frames (AtomData Cell (Record × Effect.Carrier))) state)
      (canonicalLayout (generationAfter clause.writes generation) (cursor+1)) environment
      (fun name => clause.after name environment.2.values) (cursor+1) environment.2.tail := by
  let active := clause.firing member (old := state.frame) (selectionFor clause.writes generation cursor)
  let after := active.result (frames (AtomData Cell (Record × Effect.Carrier))) state
  have information := (clause.information_iff member state _ environment).mp satisfies
  have headMatch : clause.pendingTerm environment.2 =
      state.label (Occurrence.request cursor) environment.1 := by
    exact information.2.1 (clause.pendingTerm, Occurrence.request cursor) List.mem_cons_self
  have cursorSame : environment.2.cursor = cursor :=
    (AtomData.pending.inj (headMatch.trans view.request)).1
  refine ⟨?_, satisfies, ?_, ?_⟩
  · change MeTTaCalculus.OccurrenceCommits.fire state.present
      ((selectionFor clause.writes generation cursor).commit (T := Unit)) = _
    exact (congrArg (fun present => MeTTaCalculus.OccurrenceCommits.fire present
      ((selectionFor clause.writes generation cursor).commit (T := Unit))) view.exact).trans
      (canonical_present_after clause.writes generation cursor)
  · intro name
    change after.label (row (generationAfter clause.writes generation) name) environment =
      AtomData.field name (clause.after name environment.2.values)
    by_cases written : name ∈ clause.writes
    · have rowSame : row (generationAfter clause.writes generation) name = nextRow generation name := by
        simp [row, nextRow, generationAfter, written]
      have made : (nextRow generation name,
          fun values : (extend state.frame clause.localFrame).Carrier => clause.afterTerm name values.2) ∈
          active.selection.made.zip (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce := by
        apply List.mem_cons_of_mem
        change (nextRow generation name,
          fun values : (extend state.frame clause.localFrame).Carrier => clause.afterTerm name values.2) ∈
          (clause.writes.map (nextRow generation)).zip
            ((clause.writes.map clause.afterTerm).map
              (fun term (values : (extend state.frame clause.localFrame).Carrier) => term values.2))
        rw [List.map_map, List.zip_map']
        exact List.mem_map.mpr ⟨name, written, rfl⟩
      have labelled := congrFun (RuleSyntax.Firing.result_label_made active admitted.1 made) environment
      exact (congrArg (fun occurrence => after.label occurrence environment) rowSame).trans labelled
    · have rowSame : row (generationAfter clause.writes generation) name = row generation name := by
        simp [row, generationAfter, written]
      have missing : row generation name ∉ active.selection.made := by
        intro inside
        rcases List.mem_cons.mp inside with impossible | inside
        · cases impossible
        · obtain ⟨other, _, same⟩ := List.mem_map.mp inside
          have equal := Occurrence.field.inj same
          rcases equal with ⟨rfl, impossible⟩
          omega
      have readMember : name ∈ Field.all.filter (fun field => field ∉ clause.writes) :=
        List.mem_filter.mpr ⟨NativeFieldExecution.field_member name, by simpa using written⟩
      have readPair : (clause.beforeTerm name, row generation name) ∈
          clause.rule.body.read.zip (selectionFor clause.writes generation cursor).read := by
        change (clause.beforeTerm name, row generation name) ∈
          ((Field.all.filter (fun field => field ∉ clause.writes)).map clause.beforeTerm).zip
            ((Field.all.filter (fun field => field ∉ clause.writes)).map (row generation))
        rw [List.zip_map']
        exact List.mem_map.mpr ⟨name, readMember, rfl⟩
      have matched := information.2.2.1 _ readPair
      have labelled := congrFun (RuleSyntax.Firing.result_label_other
        (X := frames (AtomData Cell (Record × Effect.Carrier))) active missing) environment
      exact (congrArg (fun occurrence => after.label occurrence environment) rowSame).trans
        (labelled.trans (matched.symm.trans
          (congrArg (AtomData.field name) (clause.unchanged name written environment.2.values).symm)))
  · have made : (Occurrence.request (cursor+1),
        fun values : (extend state.frame clause.localFrame).Carrier => clause.residualTerm values.2) ∈
        active.selection.made.zip (active.opened (frames (AtomData Cell (Record × Effect.Carrier)))).produce :=
      List.mem_cons_self
    have labelled := congrFun (RuleSyntax.Firing.result_label_made active admitted.1 made) environment
    exact labelled.trans (congrArg (fun serial => AtomData.pending serial environment.2.tail)
      (congrArg (fun serial => serial+1) cursorSame))

end QueueClause

variable {ops : Operations} (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)

theorem information_iff (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat)
    (environment : (extend state.frame (localFrame table model domains index)).Carrier) :
    Satisfies ((firing table model domains contract allow (old := state.frame) index generation cursor).information
      (frames (Atom ops model)) state) environment ↔
      Satisfies state.knowledge environment.1 ∧
      PreparedRules.Matches (rule table model domains contract allow index).body.take
        (selection table index generation cursor).taken
        (fun occurrence => state.label occurrence environment.1) environment.2 ∧
      PreparedRules.Matches (rule table model domains contract allow index).body.read
        (selection table index generation cursor).read
        (fun occurrence => state.label occurrence environment.1) environment.2 ∧
      obligation table model contract allow index environment.2.values environment.2.effect := by
  exact QueueClause.information_iff (nativeClause table model domains contract allow index)
    (rule_member table model domains contract allow index) state
    (selection table index generation cursor) environment

theorem holds_iff (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat)
    {later : Frame.{w+1}}
    (substitution : Hom (extend state.frame (localFrame table model domains index)) later) :
    (firing table model domains contract allow (old := state.frame) index generation cursor).Holds
      (frames (Atom ops model)) state substitution ↔
      ∀ environment, obligation table model contract allow index
        (substitution environment).2.values (substitution environment).2.effect := by
  exact QueueClause.holds_iff (nativeClause table model domains contract allow index)
    (rule_member table model domains contract allow index) state
    (selection table index generation cursor) substitution

/-- The told equality is part of the actual information. It constrains the
same locals at every later solution, including the result and permission. -/
theorem asks_from_information (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    (frames (Atom ops model)).Entails
      ((firing table model domains contract allow (old := state.frame) index generation cursor).information
        (frames (Atom ops model)) state)
      (fun _ substitution =>
        (firing table model domains contract allow (old := state.frame) index generation cursor).Holds
          (frames (Atom ops model)) state substitution) := by
  intro later substitution modeled
  apply (holds_iff table model domains contract allow state index generation cursor substitution).mpr
  intro environment
  have satisfies := (InterpretedFrames.models_iff substitution _).mp modeled environment
  exact ((information_iff table model domains contract allow state index generation cursor
    (substitution environment)).mp satisfies).2.2.2

/-- This existential is obtained from the interpreted frame's actual
solvability judgment. It includes the old knowledge and every field/request
equation, rather than a supplied admitted-transition predicate. -/
theorem information_solvable_iff (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    (frames (Atom ops model)).Solvable
      ((firing table model domains contract allow (old := state.frame) index generation cursor).information
        (frames (Atom ops model)) state) ↔
      ∃ (old : state.frame.Carrier) (locals : Local table model index),
        Satisfies state.knowledge old ∧
        PreparedRules.Matches (rule table model domains contract allow index).body.take
          (selection table index generation cursor).taken (fun occurrence => state.label occurrence old) locals ∧
        PreparedRules.Matches (rule table model domains contract allow index).body.read
          (selection table index generation cursor).read (fun occurrence => state.label occurrence old) locals ∧
        obligation table model contract allow index locals.values locals.effect := by
  exact QueueClause.information_solvable_iff (nativeClause table model domains contract allow index)
    (rule_member table model domains contract allow index) state (selection table index generation cursor)

theorem firing_shapes (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    (firing table model domains contract allow (old := state.frame) index generation cursor).Shapes
      (frames (Atom ops model)) state := by
  refine ⟨firing_fresh table model domains contract allow state index generation cursor,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · change (Occurrence.request cursor :: (table index).writes.map (row generation)).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, (table index).writes_distinct.map (row_injective generation)⟩
    simp [row]
  · change (Occurrence.request (cursor+1) :: (table index).writes.map (nextRow generation)).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, (table index).writes_distinct.map (nextRow_injective generation)⟩
    simp [nextRow]
  · simp only [firing, canonical, rule_unfold, selection, List.length_cons, List.length_map]
  · simp only [firing, canonical, rule_unfold, selection, List.length_map]
  · simp only [firing, canonical, rule_unfold, selection, List.length_cons, List.length_map]

theorem field_in_support (layout : Layout) (field : Field) : layout.field field ∈ layout.support := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨field, List.mem_toFinset.mpr ?_, rfl⟩
  cases field <;> simp [Field.all]

theorem physical_enabled (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    Enabled (fun _ : Occurrence => ()) (canonicalLayout generation cursor).support
      ((selection table index generation cursor).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (Occurrence.request cursor :: (table index).writes.map (row generation)).toFinset ⊆ _
    intro occurrence member
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with rfl | member
    · exact Finset.mem_insert_self _ _
    · obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
      exact field_in_support _ field
  · change ((table index).reads.map (row generation)).toFinset ⊆ _
    intro occurrence member
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact field_in_support _ field
  · change Disjoint (Occurrence.request cursor :: (table index).writes.map (row generation)).toFinset
      ((table index).reads.map (row generation)).toFinset
    apply Finset.disjoint_left.mpr
    intro occurrence taken read
    obtain ⟨field, fieldRead, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp read)
    rcases List.mem_cons.mp (List.mem_toFinset.mp taken) with same | taken
    · cases same
    · obtain ⟨other, written, same⟩ := List.mem_map.mp taken
      have equal := row_injective generation same
      subst other
      exact NativeFieldExecution.read_not_written (table index) field fieldRead written
  · change Disjoint (Occurrence.request (cursor+1) :: (table index).writes.map (nextRow generation)).toFinset
      (canonicalLayout generation cursor).support
    apply Finset.disjoint_left.mpr
    intro occurrence made old
    rcases List.mem_cons.mp (List.mem_toFinset.mp made) with rfl | made
    · rcases Finset.mem_insert.mp old with same | old
      · have impossible := Occurrence.request.inj same
        omega
      · obtain ⟨field, _, same⟩ := Finset.mem_image.mp old
        cases same
    · obtain ⟨field, _, rfl⟩ := List.mem_map.mp made
      rcases Finset.mem_insert.mp old with same | old
      · cases same
      · obtain ⟨other, _, same⟩ := Finset.mem_image.mp old
        have parts := Occurrence.field.inj same
        have sameField : other = field := parts.1
        subst other
        have impossible : generation field = generation field+1 := parts.2
        omega
  · intro query member
    cases member

theorem admission_iff (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat)
    (present : state.present = (canonicalLayout generation cursor).support) :
    (RuleSyntax.step (frames (Atom ops model)) Occurrence extensions
      (program table model domains contract allow)).Admits
      (s := state) (firing table model domains contract allow index generation cursor) ↔
      (frames (Atom ops model)).Solvable
        ((firing table model domains contract allow (old := state.frame) index generation cursor).information
          (frames (Atom ops model)) state) := by
  constructor
  · intro admitted
    exact admitted.2.2.1
  · intro solvable
    refine ⟨firing_shapes table model domains contract allow state index generation cursor, ?_, solvable,
      asks_from_information table model domains contract allow state index generation cursor⟩
    change Enabled _ state.present ((selection table index generation cursor).commit (T := Unit))
    rw [present]
    exact physical_enabled table index generation cursor

theorem admitted_of_view (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat) (environment : state.frame.Carrier)
    (fields : NativeFieldPacking.Fields ops model) (pending : List (Event ops model))
    (view : View model state (canonicalLayout generation cursor) environment fields cursor pending)
    (locals : Local table model index)
    (same : ∀ name, fields name = model.denote ((table index).before name) locals.values)
    (sameCursor : locals.cursor = cursor)
    (samePending : pending = (recordValue table model index locals.values, locals.effect) :: locals.tail)
    (valid : obligation table model contract allow index locals.values locals.effect) :
    (RuleSyntax.step (frames (Atom ops model)) Occurrence extensions
      (program table model domains contract allow)).Admits
      (s := state) (firing table model domains contract allow index generation cursor) := by
  have matched := QueueClause.matches_of_view (nativeClause table model domains contract allow index)
    state generation cursor environment fields pending view locals same sameCursor samePending
  apply (admission_iff table model domains contract allow state index generation cursor view.exact).mpr
  exact (information_solvable_iff table model domains contract allow state index generation cursor).mpr
    ⟨environment, locals, view.solved, matched.1, matched.2, valid⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns
