import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots

/-!
# Executed snapshot-copy controls

Five actual selections copy three source cells, including equal cached
suspensions at different indices and an undemanded suspension. Every result
is the preceding world's ordinary firing result; no store is reconstructed
between events. Negative controls exercise admission, not a separate model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots.Controls

open SnapshotCopy
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

def cached : Suspension := ⟨.emit 9 (.ret (.var 0)),[.sym 7],.done (.sym 7)⟩
def pending : Suspension := ⟨.emit 5 (.force (.var 0)),[.need 0],.pending⟩
def store : Store := ⟨[cached,cached,pending],[9,9,3]⟩
def initial := encode 5 0 store

def startRule : RuleInstance (Row Suspension) := beginRule 5 0 1 3 store.trace
def firstRule : RuleInstance (Row Suspension) := copyRule 5 0 1 0 2 cached
def secondRule : RuleInstance (Row Suspension) := copyRule 5 0 1 1 1 cached
def thirdRule : RuleInstance (Row Suspension) := copyRule 5 0 1 2 0 pending
def doneRule : RuleInstance (Row Suspension) := finishRule 5 0 1 3 store.trace

def startSelection : Selection (Occurrence Suspension) :=
  ⟨[(6,.request 5 0)],[(1,.ready 0),(2,.metadata 0 3 store.trace)],
    [(7,.allocated 1),(8,.metadata 1 3 store.trace),(9,.cursor 5 0 1 0 3)]⟩
def firstSelection : Selection (Occurrence Suspension) :=
  ⟨[(9,.cursor 5 0 1 0 3)],[(1,.ready 0),(3,.cell 0 0 cached)],
    [(10,.cell 1 0 cached),(11,.cursor 5 0 1 1 2)]⟩
def secondSelection : Selection (Occurrence Suspension) :=
  ⟨[(11,.cursor 5 0 1 1 2)],[(1,.ready 0),(4,.cell 0 1 cached)],
    [(12,.cell 1 1 cached),(13,.cursor 5 0 1 2 1)]⟩
def thirdSelection : Selection (Occurrence Suspension) :=
  ⟨[(13,.cursor 5 0 1 2 1)],[(1,.ready 0),(5,.cell 0 2 pending)],
    [(14,.cell 1 2 pending),(15,.cursor 5 0 1 3 0)]⟩
def doneSelection : Selection (Occurrence Suspension) :=
  ⟨[(15,.cursor 5 0 1 3 0)],
    [(1,.ready 0),(2,.metadata 0 3 store.trace),(8,.metadata 1 3 store.trace)],
    [(16,.ready 1),(17,.reply 5 1)]⟩

def started := startSelection.result label startRule initial
def afterFirst := firstSelection.result label firstRule started
def afterSecond := secondSelection.result label secondRule afterFirst
def afterThird := thirdSelection.result label thirdRule afterSecond
def finished := doneSelection.result label doneRule afterThird

theorem start_valid : startSelection.Valid action label startRule initial := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ startSelection.problem label startRule initial, equation.1 = equation.2
    decide +kernel
  · intro check member assignment _
    have same : check = .absent (.allocated 1) := List.mem_singleton.mp member
    subst check
    change ∀ occurrence ∈ initial.present, Row.allocated 1 ≠ label occurrence
    decide +kernel

theorem first_valid : firstSelection.Valid action label firstRule started := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ firstSelection.problem label firstRule started, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem second_valid : secondSelection.Valid action label secondRule afterFirst := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ secondSelection.problem label secondRule afterFirst, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem third_valid : thirdSelection.Valid action label thirdRule afterSecond := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ thirdSelection.problem label thirdRule afterSecond, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem done_valid : doneSelection.Valid action label doneRule afterThird := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ doneSelection.problem label doneRule afterThird, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

def startFiring : Firing startRule (6,.request 5 0) initial started :=
  ⟨startSelection,rfl,start_valid,rfl⟩
def firstFiring : Firing firstRule (9,.cursor 5 0 1 0 3) started afterFirst :=
  ⟨firstSelection,rfl,first_valid,rfl⟩
def secondFiring : Firing secondRule (11,.cursor 5 0 1 1 2) afterFirst afterSecond :=
  ⟨secondSelection,rfl,second_valid,rfl⟩
def thirdFiring : Firing thirdRule (13,.cursor 5 0 1 2 1) afterSecond afterThird :=
  ⟨thirdSelection,rfl,third_valid,rfl⟩
def doneFiring : Firing doneRule (15,.cursor 5 0 1 3 0) afterThird finished :=
  ⟨doneSelection,rfl,done_valid,rfl⟩

theorem complete_execution : Execution 5 0 1
    [.begin 3 store.trace,.copy 0 2 cached,.copy 1 1 cached,.copy 2 0 pending,.finish 3 store.trace] initial finished :=
  .cons _ _ startFiring (.cons _ _ firstFiring (.cons _ _ secondFiring
    (.cons _ _ thirdFiring (.cons _ _ doneFiring (.nil finished)))))

theorem started_progress : Progress started 5 0 1 store.cells store.trace 0 3 (9,.cursor 5 0 1 0 3) := by
  obtain ⟨token,progress⟩ := progress_after_begin (encoded_snapshot 5 0 store)
    (encoded_fresh store (by decide : 0 ≠ 1)) startFiring
  have same := progress.cursorUnique (9,.cursor 5 0 1 0 3) (by decide) 5 0 0 3 rfl
  exact same.symm ▸ progress

theorem finished_snapshot : Completed finished 5 0 1 store.cells store.trace := by
  have execution : Execution 5 0 1
      [.copy 0 2 cached,.copy 1 1 cached,.copy 2 0 pending,.finish 3 store.trace] started finished :=
    .cons _ _ firstFiring (.cons _ _ secondFiring (.cons _ _ thirdFiring (.cons _ _ doneFiring (.nil finished))))
  exact ((execution.ready_iff_completed started_progress).mp
    ⟨(16,.ready 1),by decide,rfl⟩).1

theorem equal_payloads_keep_two_cells :
    (10,.cell 1 0 cached) ∈ finished.present ∧ (12,.cell 1 1 cached) ∈ finished.present ∧
      (10,Row.cell 1 0 cached) ≠ (12,Row.cell 1 1 cached) := by decide +kernel

theorem undemanded_code_and_captures_survive : (14,.cell 1 2 pending) ∈ finished.present := by decide +kernel
theorem original_physical_cells_survive :
    (3,.cell 0 0 cached) ∈ finished.present ∧ (4,.cell 0 1 cached) ∈ finished.present ∧
      (5,.cell 0 2 pending) ∈ finished.present := by decide +kernel
theorem trace_order_and_repetitions_survive : (8,.metadata 1 3 [9,9,3]) ∈ finished.present := by decide +kernel
theorem intermediate_equations_are_retained : started.equations.IsPrefix finished.equations ∧
    finished.equations.length = 16 := by decide +kernel

def wrongIndexSelection := { firstSelection with read := [(1,.ready 0),(4,.cell 0 1 cached)] }

theorem equal_value_at_wrong_index_refused : ¬ wrongIndexSelection.Valid action label firstRule started := by
  intro valid
  obtain ⟨assignment,solved⟩ := valid.consistent
  have impossible := solved (.cell 0 0 cached,.cell 0 1 cached) (by decide)
  change Row.cell 0 0 cached = Row.cell 0 1 cached at impossible
  cases impossible

theorem consumed_cursor_cannot_be_replayed : ¬ firstSelection.Valid action label firstRule afterFirst := by
  intro valid
  have old := valid.occurrences.taken_subset (by decide : (9,.cursor 5 0 1 0 3) ∈ firstSelection.commit.taken)
  exact (by decide : (9,.cursor 5 0 1 0 3) ∉ afterFirst.present) old

theorem incomplete_copy_cannot_finish :
    ¬ ∃ after, Nonempty (Firing doneRule (11,.cursor 5 0 1 1 2) afterFirst after) := by
  rintro ⟨after,⟨firing⟩⟩
  have impossible := firing.take_value (.cursor 5 0 1 3 0) rfl
  cases impossible

theorem allocated_destination_cannot_be_reused (token : Occurrence Suspension) (after : World Suspension) :
    ¬ Nonempty (Firing startRule token finished after) :=
  allocated_refuses_begin finished_snapshot.destinationSnapshot.allocated

def missingSource := { started with present := started.present.erase (3,.cell 0 0 cached) }

theorem missing_source_cell_refuses_its_copy_step (token : Occurrence Suspension) (after : World Suspension) :
    ¬ Nonempty (Firing firstRule token missingSource after) := by
  rintro ⟨firing⟩
  obtain ⟨occurrence,present,same⟩ := firing.read_rows (.cell 0 0 cached) (by simp [firstRule,copyRule])
  have absent : ∀ occurrence ∈ missingSource.present, label occurrence ≠ .cell 0 0 cached := by decide +kernel
  exact absent occurrence present same

/-- Internal cells are observable before readiness if a context is allowed
to read them. Completion gating alone is not a public atomicity theorem. -/
theorem partial_copy_is_visible_to_an_unrestricted_reader :
    Has afterFirst.present (.cell 1 0 cached) ∧ ¬ Has afterFirst.present (.cell 1 1 cached) ∧
      ¬ Has afterFirst.present (.ready 1) := by
  refine ⟨⟨(10,.cell 1 0 cached),by decide,rfl⟩,?_,?_⟩
  · rintro ⟨occurrence,present,same⟩
    exact (by decide : ∀ occurrence ∈ afterFirst.present, label occurrence ≠ .cell 1 1 cached)
      occurrence present same
  · rintro ⟨occurrence,present,same⟩
    exact (by decide : ∀ occurrence ∈ afterFirst.present, label occurrence ≠ .ready 1)
      occurrence present same

/-- An external writer can forge a completed cursor. The core correctly
executes the given rule, but that execution does not certify copy coverage. -/
def forgedEnd : World Suspension :=
  { started with
    present := insert (15,.cursor 5 0 1 3 0) (started.present.erase (9,.cursor 5 0 1 0 3)) }
def forgedFinished := doneSelection.result label doneRule forgedEnd

theorem forged_cursor_admits_the_finish_rule : doneSelection.Valid action label doneRule forgedEnd := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ doneSelection.problem label doneRule forgedEnd, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem forged_readiness_does_not_certify_a_snapshot :
    Step action label doneRule forgedEnd forgedFinished ∧ Has forgedFinished.present (.ready 1) ∧
      ¬ Snapshot forgedFinished.present 1 store.cells store.trace := by
  refine ⟨⟨doneSelection,forged_cursor_admits_the_finish_rule,rfl⟩,⟨(16,.ready 1),by decide,rfl⟩,?_⟩
  intro snapshot
  obtain ⟨occurrence,present,same⟩ := (snapshot.cells.exact 0 cached).mpr rfl
  exact (by decide : ∀ occurrence ∈ forgedFinished.present, label occurrence ≠ .cell 1 0 cached)
    occurrence present same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots.Controls
