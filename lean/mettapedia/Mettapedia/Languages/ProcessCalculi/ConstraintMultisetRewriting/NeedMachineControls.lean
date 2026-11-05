import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

/-!
# A physical control, copy and requested-edit episode

The old branch retains its cached 7. The requested edit creates a new
snapshot with cached 42, then resumes a continuation whose saved branch
still points to the old snapshot. All worlds below are actual ordinary
firing results, with the complete prior equation store retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.Controls

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Suspension Store)

def cached : Suspension := ⟨.ret (.sym 7),[],.done (.sym 7)⟩
def changed : Suspension := {cached with memo := .done (.sym 42)}
def saved : List (Frame Nat) := [.later (.forceVal 0 (.need 0))]
def intent : Intent [] := .commitOk 0 (.sym 42) 0 [] saved
def resume : Resume := .task (.forceVal none (.sym 42))
  [.later (.commitK 0 []),.later (.forceVal (some 0) (.need 0))]

def initial : World := ⟨[],{
  (0,.heap (.allocated 0)),(1,.heap (.ready 0)),(2,.heap (.metadata 0 1 [3])),
  (3,.heap (.cell 0 0 cached)),(4,.control 1 intent.plan.input)}⟩

def beginRule := startRule 1 intent
def prepareRule := copyRule 1 intent.plan.input intent.plan.reads 0 (.memo 0 (.done (.sym 42))) resume (.begin 1 [3])
def copyCellRule := copyRule 1 intent.plan.input intent.plan.reads 0 (.memo 0 (.done (.sym 42))) resume (.copy 0 0 cached)
def finishRule := copyRule 1 intent.plan.input intent.plan.reads 0 (.memo 0 (.done (.sym 42))) resume (.finish 1 [3])
def updateRule := commitRule 1 intent.plan.input intent.plan.reads 0 resume (.memo 0 cached (.done (.sym 42)))

def beginSelection : Selection Occurrence :=
  ⟨[(4,.control 1 intent.plan.input)],[(1,.heap (.ready 0))],
    [(5,.waiting 1 intent.plan),(6,.heap (.request 1 0))]⟩
def prepareSelection : Selection Occurrence :=
  ⟨[(6,.heap (.request 1 0))],
    [(1,.heap (.ready 0)),(2,.heap (.metadata 0 1 [3])),(5,.waiting 1 intent.plan)],
    [(7,.heap (.allocated 1)),(8,.heap (.metadata 1 1 [3])),(9,.heap (.cursor 1 0 1 0 1))]⟩
def copyCellSelection : Selection Occurrence :=
  ⟨[(9,.heap (.cursor 1 0 1 0 1))],
    [(1,.heap (.ready 0)),(3,.heap (.cell 0 0 cached)),(5,.waiting 1 intent.plan)],
    [(10,.heap (.cell 1 0 cached)),(11,.heap (.cursor 1 0 1 1 0))]⟩
def finishSelection : Selection Occurrence :=
  ⟨[(11,.heap (.cursor 1 0 1 1 0))],
    [(1,.heap (.ready 0)),(2,.heap (.metadata 0 1 [3])),(8,.heap (.metadata 1 1 [3])),(5,.waiting 1 intent.plan)],
    [(12,.heap (.ready 1)),(13,.heap (.reply 1 1))]⟩
def updateSelection : Selection Occurrence :=
  ⟨[(5,.waiting 1 intent.plan),(13,.heap (.reply 1 1)),(10,.heap (.cell 1 0 cached))],
    [(12,.heap (.ready 1))],
    [(14,.control 2 (resumeAt 1 resume)),(16,.heap (.cell 1 0 changed))]⟩

def started := beginSelection.result label beginRule initial
def prepared := prepareSelection.result label prepareRule started
def copied := copyCellSelection.result label copyCellRule prepared
def finished := finishSelection.result label finishRule copied
def resumed := updateSelection.result label updateRule finished

local macro "positive_selection" : tactic => `(tactic|
  (refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
   · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
   · change ∀ equation : Equation Row, equation ∈ _ → equation.1 = equation.2
     decide +kernel
   · intro check member; cases member))

theorem begin_valid : beginSelection.Valid action label beginRule initial := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ beginSelection.problem label beginRule initial, equation.1 = equation.2
    decide +kernel
  · intro check member assignment _
    have same : check = .absent (.heap (.allocated 1)) := List.mem_singleton.mp member
    subst check
    change ∀ occurrence ∈ initial.present, Row.heap (.allocated 1) ≠ label occurrence
    decide +kernel

theorem prepare_valid : prepareSelection.Valid action label prepareRule started := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ prepareSelection.problem label prepareRule started, equation.1 = equation.2
    decide +kernel
  · intro check member assignment _
    have same : check = .absent (.heap (.allocated 1)) := List.mem_singleton.mp member
    subst check
    change ∀ occurrence ∈ started.present, Row.heap (.allocated 1) ≠ label occurrence
    decide +kernel

theorem copy_valid : copyCellSelection.Valid action label copyCellRule prepared := by positive_selection
theorem finish_valid : finishSelection.Valid action label finishRule copied := by positive_selection
theorem update_valid : updateSelection.Valid action label updateRule finished := by positive_selection

theorem resumed_control_keeps_the_saved_branch :
    (14,.control 2 (.task (.forceVal 1 (.sym 42)) [.later (.commitK 0 []),.later (.forceVal 0 (.need 0))]))
      ∈ resumed.present := by decide +kernel

theorem old_and_new_memos_remain_separate :
    (3,.heap (.cell 0 0 cached)) ∈ resumed.present ∧ (16,.heap (.cell 1 0 changed)) ∈ resumed.present := by
  decide +kernel

theorem waiting_control_is_consumed : (5,.waiting 1 intent.plan) ∉ resumed.present := by decide +kernel

theorem completed_reply_is_not_reissued : ¬ Has resumed.present (.heap (.reply 1 1)) := by
  rintro ⟨occurrence,present,same⟩
  exact (by decide : ∀ occurrence ∈ resumed.present, label occurrence ≠ .heap (.reply 1 1)) occurrence present same

theorem completed_episode_cannot_replay_its_update : ¬ updateSelection.Valid action label updateRule resumed := by
  intro valid
  have present := valid.occurrences.taken_subset
    (by decide : (5,.waiting 1 intent.plan) ∈ updateSelection.commit.taken)
  exact waiting_control_is_consumed present

theorem every_intermediate_equation_survives :
    started.equations.IsPrefix resumed.equations ∧ resumed.equations.length = 19 := by decide +kernel

def firstResults : List (Result Nat) := [(.ok (.sym 42),1)]
def lastResults : List (Result Nat) := [(.ok (.sym 7),0)]
def i0 : Intent [] := .forceWhnf 1 (.sym 42) rfl [.later (.commitK 0 []),.later (.forceVal 0 (.need 0))]
def i1 : Intent [] := .laterReturn firstResults (.commitK 0 []) [.later (.forceVal 0 (.need 0))]
def i2 : Intent [] := .commitNil 0 [.append firstResults,.later (.forceVal 0 (.need 0))]
def i3 : Intent [] := .appendReturn firstResults [] [.later (.forceVal 0 (.need 0))]
def i4 : Intent [] := .laterReturn firstResults (.forceVal 0 (.need 0)) []
def i5 : Intent [] := .forceDone 0 0 cached (.sym 7) rfl [.append firstResults]
def i6 : Intent [] := .forceWhnf 0 (.sym 7) rfl [.append firstResults]
def i7 : Intent [] := .appendReturn firstResults lastResults []
def doneControl : Control Nat := .returned [(.ok (.sym 42),1),(.ok (.sym 7),0)] []

def directSelection (old fresh : Nat) (input output : Control Nat) (reads : List Occurrence) : Selection Occurrence :=
  ⟨[(old,.control 2 input)],reads,[(fresh,.control 2 output)]⟩

def p0 := directSelection 14 17 i0.plan.input i1.plan.input []
def p1 := directSelection 17 18 i1.plan.input i2.plan.input []
def p2 := directSelection 18 19 i2.plan.input i3.plan.input []
def p3 := directSelection 19 20 i3.plan.input i4.plan.input []
def p4 := directSelection 20 21 i4.plan.input i5.plan.input []
def p5 := directSelection 21 22 i5.plan.input i6.plan.input [(1,.heap (.ready 0)),(3,.heap (.cell 0 0 cached))]
def p6 := directSelection 22 23 i6.plan.input i7.plan.input []
def p7 := directSelection 23 24 i7.plan.input doneControl []

def w0 := p0.result label (startRule 2 i0) resumed
def w1 := p1.result label (startRule 2 i1) w0
def w2 := p2.result label (startRule 2 i2) w1
def w3 := p3.result label (startRule 2 i3) w2
def w4 := p4.result label (startRule 2 i4) w3
def w5 := p5.result label (startRule 2 i5) w4
def w6 := p6.result label (startRule 2 i6) w5
def terminal := p7.result label (startRule 2 i7) w6

theorem v0 : p0.Valid action label (startRule 2 i0) resumed := by positive_selection
theorem v1 : p1.Valid action label (startRule 2 i1) w0 := by positive_selection
theorem v2 : p2.Valid action label (startRule 2 i2) w1 := by positive_selection
theorem v3 : p3.Valid action label (startRule 2 i3) w2 := by positive_selection
theorem v4 : p4.Valid action label (startRule 2 i4) w3 := by positive_selection
theorem v5 : p5.Valid action label (startRule 2 i5) w4 := by positive_selection
theorem v6 : p6.Valid action label (startRule 2 i6) w5 := by positive_selection
theorem v7 : p7.Valid action label (startRule 2 i7) w6 := by positive_selection

theorem both_result_values_and_snapshot_references_are_retained :
    (24,.control 2 doneControl) ∈ terminal.present ∧
      (3,.heap (.cell 0 0 cached)) ∈ terminal.present ∧ (16,.heap (.cell 1 0 changed)) ∈ terminal.present ∧
      terminal.equations.length = 29 := by decide +kernel

def wrongOperation := commitRule 1 intent.plan.input intent.plan.reads 0 resume (.memo 0 cached (.done (.sym 99)))

theorem another_operation_cannot_use_the_waiting_control :
    ¬ ∃ after, Step action label wrongOperation finished after := by
  rintro ⟨after,picked,valid,_⟩
  let wrong : Plan := ⟨intent.plan.input,intent.plan.reads,.edit 0 (.memo 0 (.done (.sym 99))) resume⟩
  obtain ⟨occurrence,present,same⟩ := Selected.take_rows valid (.waiting 1 wrong)
    (by simp [wrongOperation,commitRule,wrong,NeedStoreOperations.Event.operation])
  exact (by decide : ∀ occurrence ∈ finished.present, label occurrence ≠ .waiting 1 wrong) occurrence present same

theorem no_operation_commits_before_copy_completion (event : NeedStoreOperations.Event) :
    ¬ ∃ after, Step action label (commitRule 1 intent.plan.input intent.plan.reads 0 resume event) copied after := by
  rintro ⟨after,picked,valid,_⟩
  obtain ⟨occurrence,present,same⟩ := Selected.read_rows valid (.heap (.ready 1))
    (by cases event <;> simp [commitRule,NeedStoreOperations.Event.rule])
  exact (by decide : ∀ occurrence ∈ copied.present, label occurrence ≠ .heap (.ready 1)) occurrence present same

def wrongResume : Resume := .task (.forceVal none (.sym 42))
  [.later (.commitK 0 []),.later (.forceVal none (.need 0))]

theorem another_continuation_cannot_use_the_waiting_control :
    ¬ ∃ after, Step action label
      (commitRule 1 intent.plan.input intent.plan.reads 0 wrongResume (.memo 0 cached (.done (.sym 42)))) finished after := by
  rintro ⟨after,picked,valid,_⟩
  let wrong : Plan := ⟨intent.plan.input,intent.plan.reads,.edit 0 (.memo 0 (.done (.sym 42))) wrongResume⟩
  obtain ⟨occurrence,present,same⟩ := Selected.take_rows valid (.waiting 1 wrong)
    (by simp [commitRule,wrong,NeedStoreOperations.Event.operation])
  exact (by decide : ∀ occurrence ∈ finished.present, label occurrence ≠ .waiting 1 wrong) occurrence present same

theorem actual_complete_controlled_execution : Path [] initial terminal := by
  have start : Executes [] initial started := ⟨beginRule,.start 1 intent,⟨beginSelection,begin_valid,rfl⟩⟩
  have prepare : Executes [] started prepared := ⟨prepareRule,.copy _ _ _ _ _ _ _,⟨prepareSelection,prepare_valid,rfl⟩⟩
  have copy : Executes [] prepared copied := ⟨copyCellRule,.copy _ _ _ _ _ _ _,⟨copyCellSelection,copy_valid,rfl⟩⟩
  have finish : Executes [] copied finished := ⟨finishRule,.copy _ _ _ _ _ _ _,⟨finishSelection,finish_valid,rfl⟩⟩
  have update : Executes [] finished resumed := ⟨updateRule,.commit _ _ _ _ _ _,⟨updateSelection,update_valid,rfl⟩⟩
  have s0 : Executes [] resumed w0 := ⟨startRule 2 i0,.start 2 i0,⟨p0,v0,rfl⟩⟩
  have s1 : Executes [] w0 w1 := ⟨startRule 2 i1,.start 2 i1,⟨p1,v1,rfl⟩⟩
  have s2 : Executes [] w1 w2 := ⟨startRule 2 i2,.start 2 i2,⟨p2,v2,rfl⟩⟩
  have s3 : Executes [] w2 w3 := ⟨startRule 2 i3,.start 2 i3,⟨p3,v3,rfl⟩⟩
  have s4 : Executes [] w3 w4 := ⟨startRule 2 i4,.start 2 i4,⟨p4,v4,rfl⟩⟩
  have s5 : Executes [] w4 w5 := ⟨startRule 2 i5,.start 2 i5,⟨p5,v5,rfl⟩⟩
  have s6 : Executes [] w5 w6 := ⟨startRule 2 i6,.start 2 i6,⟨p6,v6,rfl⟩⟩
  have s7 : Executes [] w6 terminal := ⟨startRule 2 i7,.start 2 i7,⟨p7,v7,rfl⟩⟩
  apply (Relation.ReflTransGen.single start).trans
  apply (Relation.ReflTransGen.single prepare).trans
  apply (Relation.ReflTransGen.single copy).trans
  apply (Relation.ReflTransGen.single finish).trans
  apply (Relation.ReflTransGen.single update).trans
  apply (Relation.ReflTransGen.single s0).trans
  apply (Relation.ReflTransGen.single s1).trans
  apply (Relation.ReflTransGen.single s2).trans
  apply (Relation.ReflTransGen.single s3).trans
  apply (Relation.ReflTransGen.single s4).trans
  apply (Relation.ReflTransGen.single s5).trans
  apply (Relation.ReflTransGen.single s6).trans
  exact Relation.ReflTransGen.single s7

def oldStore : Store := ⟨[cached],[3]⟩
def newStore : Store := oldStore.setMemo 0 (.done (.sym 42))
def sourceInitial : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control :=
  .task (.commitK 0 [(.ok (.sym 42),oldStore)]) [.later (.forceVal oldStore (.need 0))]
def sourceFinal : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control :=
  .returned [(.ok (.sym 42),newStore),(.ok (.sym 7),oldStore)] []

theorem independent_source_finishes_with_both_stores :
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.runFuel [] 50 sourceInitial = sourceFinal := by
  rfl

theorem independent_source_path :
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Path [] sourceInitial sourceFinal := by
  simpa only [independent_source_finishes_with_both_stores] using
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.runFuel_has_path [] 50 sourceInitial

def observedResults (world : World) : Finset (List (Result Nat)) :=
  (world.present.val.filterMap fun occurrence => match occurrence.2 with
    | .control _ (.returned results []) => some results
    | _ => none).toFinset

theorem exact_terminal_answer_list : observedResults terminal = {[ (.ok (.sym 42),1),(.ok (.sym 7),0)]} := by
  decide +kernel

theorem exact_terminal_heap : heapPresent terminal.present = {
    (0,.allocated 0),(1,.ready 0),(2,.metadata 0 1 [3]),(3,.cell 0 0 cached),
    (7,.allocated 1),(8,.metadata 1 1 [3]),(12,.ready 1),(16,.cell 1 0 changed)} := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.Controls
