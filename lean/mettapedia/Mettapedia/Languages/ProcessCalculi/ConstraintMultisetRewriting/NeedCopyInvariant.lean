import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedHeapFrames

/-!
# Copy phases with a complete heap frame

The existing snapshot-copy invariant is extended with the allocation bound
and the only permitted auxiliary occurrence. This excludes leftover requests
and replies as well as forged cursors when successive edits compose.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedHeapFrames

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Store)

inductive CopyState (world : HeapWorld) (job source : Nat) (store : Store) : Nat → Prop where
  | requested (token : HeapOccurrence)
      (snapshot : SnapshotCopy.Snapshot world.present source store.cells store.trace)
      (fresh : SnapshotCopy.Fresh world.present job)
      (here : token ∈ world.present) (atToken : SnapshotCopy.label token = .request job source)
      (frame : Frame job (some token) world.present) : CopyState world job source store (store.cells.length+2)
  | copying {index remaining : Nat} {token : HeapOccurrence}
      (progress : SnapshotCopy.Progress world job source job store.cells store.trace index remaining token)
      (frame : Frame (job+1) (some token) world.present) : CopyState world job source store (remaining+1)
  | complete (token : HeapOccurrence)
      (completed : SnapshotCopy.Completed world job source job store.cells store.trace)
      (here : token ∈ world.present) (atToken : SnapshotCopy.label token = .reply job job)
      (frame : Frame (job+1) (some token) world.present) : CopyState world job source store 0

theorem CopyState.step {before after : HeapWorld} {job source rank : Nat} {store : Store}
    {selected : HeapOccurrence} (state : CopyState before job source store rank)
    (event : SnapshotCopy.Event Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Suspension)
    (firing : SnapshotCopy.Firing (event.rule job source job) selected before after) :
    ∃ nextRank, CopyState after job source store nextRank ∧ rank = nextRank+1 := by
  cases state with
  | requested token snapshot fresh here atToken frame =>
      cases event with
      | begin count trace =>
          have selectedLabel := firing.take_value (.request job source) rfl
          have selectedEq := frame.token_eq firing.token_present (by simp [selectedLabel,DataBelow])
          subst selected
          have fields := snapshot.metadata.agreement count trace
            (firing.read_rows (.metadata source count trace) (by simp [SnapshotCopy.Event.rule,SnapshotCopy.beginRule]))
          obtain ⟨rfl,rfl⟩ := fields
          obtain ⟨cursor,progress⟩ := SnapshotCopy.progress_after_begin snapshot fresh firing
          have afterFrame : Frame (job+1) (some cursor) after.present := by
            apply frame.after_firing (Nat.le_succ job) firing
            intro occurrence made
            have output := firing.made_labels made
            simp only [SnapshotCopy.Event.rule,SnapshotCopy.beginRule,List.mem_cons,List.not_mem_nil,or_false] at output
            rcases output with allocated | metadata | atCursor
            · exact Or.inl (by rw [allocated]; exact Nat.lt_succ_self job)
            · exact Or.inl (by rw [metadata]; exact Nat.lt_succ_self job)
            · exact Or.inr (congrArg some (progress.cursorUnique occurrence
                ((firing.present_iff occurrence).mpr (Or.inr made)) job source 0 store.cells.length atCursor))
          exact ⟨store.cells.length+1,.copying progress afterFrame,by omega⟩
      | copy index remaining value =>
          exact False.elim (fresh.not_has (.cursor job source job index (remaining+1))
            (by simp [SnapshotCopy.Row.mentions]) ⟨selected,firing.token_present,firing.take_value _ rfl⟩)
      | finish count trace =>
          exact False.elim (fresh.not_has (.cursor job source job count 0)
            (by simp [SnapshotCopy.Row.mentions]) ⟨selected,firing.token_present,firing.take_value _ rfl⟩)
  | copying progress frame =>
      cases event with
      | begin count trace =>
          exact False.elim (SnapshotCopy.allocated_refuses_begin progress.destinationAllocated ⟨firing⟩)
      | copy index remaining value =>
          obtain ⟨rfl,rfl,rfl⟩ := progress.copy_reflects firing
          obtain ⟨cursor,nextProgress⟩ := SnapshotCopy.progress_after_copy progress firing
          have afterFrame : Frame (job+1) (some cursor) after.present := by
            apply frame.after_firing (Nat.le_refl _) firing
            intro occurrence made
            have output := firing.made_labels made
            simp only [SnapshotCopy.Event.rule,SnapshotCopy.copyRule,List.mem_cons,List.not_mem_nil,or_false] at output
            rcases output with atCell | atCursor
            · exact Or.inl (by rw [atCell]; exact Nat.lt_succ_self job)
            · exact Or.inr (congrArg some (nextProgress.cursorUnique occurrence
                ((firing.present_iff occurrence).mpr (Or.inr made)) job source (index+1) remaining atCursor))
          exact ⟨remaining+1,.copying nextProgress afterFrame,rfl⟩
      | finish count trace =>
          obtain ⟨rfl,rfl,rfl,rfl⟩ := progress.finish_reflects firing
          have completed := SnapshotCopy.finish_completed progress firing
          obtain ⟨reply,replyHere,atReply⟩ := completed.reply
          have afterFrame : Frame (job+1) (some reply) after.present := by
            apply frame.after_firing (Nat.le_refl _) firing
            intro occurrence made
            have output := firing.made_labels made
            simp only [SnapshotCopy.Event.rule,SnapshotCopy.finishRule,List.mem_cons,List.not_mem_nil,or_false] at output
            rcases output with ready | replied
            · exact Or.inl (by rw [ready]; exact Nat.lt_succ_self job)
            · exact Or.inr (congrArg some (completed.replyUnique occurrence
                ((firing.present_iff occurrence).mpr (Or.inr made)) reply replyHere replied atReply))
          exact ⟨0,.complete reply completed replyHere atReply afterFrame,rfl⟩
  | complete token completed here atToken frame =>
      exact False.elim (completed.no_firing event ⟨firing⟩)

/-- A command admitted for final publication is backed by a completed
copy, including its unique reply and bounded auxiliary-free data frame. -/
theorem CopyState.completed_of_reply {world : HeapWorld} {job source rank : Nat} {store : Store}
    (state : CopyState world job source store rank) (replied : SnapshotCopy.Has world.present (.reply job job)) :
    rank = 0 ∧ ∃ token,
      SnapshotCopy.Completed world job source job store.cells store.trace ∧ token ∈ world.present ∧
      SnapshotCopy.label token = .reply job job ∧ Frame (job+1) (some token) world.present := by
  cases state with
  | requested token snapshot fresh here atToken frame =>
      exact False.elim (fresh.not_has (.reply job job) (by simp [SnapshotCopy.Row.mentions]) replied)
  | copying progress frame => exact False.elim (progress.notReplied replied)
  | complete token completed here atToken frame => exact ⟨rfl,token,completed,here,atToken,frame⟩

/-- Every unfinished phase has an actual next heap firing. Together with
the decreasing rank, this supplies finite completion without a source
evaluator or a scheduler premise. -/
theorem CopyState.progress {world : HeapWorld} {job source rank : Nat} {store : Store}
    (state : CopyState world job source store rank) (unfinished : 0 < rank)
    (consistent : SnapshotCopy.action.Consistent world.equations) :
    ∃ event : SnapshotCopy.Event Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Suspension,
      ∃ after, Step SnapshotCopy.action SnapshotCopy.label (event.rule job source job) world after := by
  cases state with
  | requested token snapshot fresh here atToken frame =>
      obtain ⟨after,⟨firing⟩⟩ := SnapshotCopy.begin_exists world job source job store.cells store.trace
        snapshot fresh token here atToken consistent
      exact ⟨.begin store.cells.length store.trace,after,firing.ordinary⟩
  | @copying index remaining token progress frame =>
      cases remaining with
      | zero =>
          obtain ⟨after,⟨firing⟩⟩ := SnapshotCopy.finish_exists progress
          exact ⟨.finish store.cells.length store.trace,after,firing.ordinary⟩
      | succ left =>
          obtain ⟨value,after,⟨firing⟩⟩ := SnapshotCopy.progress_has_copy progress
          exact ⟨.copy index left value,after,firing.ordinary⟩
  | complete => omega

theorem CopyState.zero_replied {world : HeapWorld} {job source : Nat} {store : Store}
    (state : CopyState world job source store 0) : SnapshotCopy.Has world.present (.reply job job) := by
  cases state with
  | complete token completed here atToken frame => exact completed.reply

theorem CopyState.rank_unique {world : HeapWorld} {job source firstRank secondRank : Nat}
    {firstStore secondStore : Store}
    (first : CopyState world job source firstStore firstRank)
    (second : CopyState world job source secondStore secondRank) : firstRank = secondRank := by
  cases first with
  | requested token snapshot fresh here atToken frame =>
      cases second with
      | requested otherToken otherSnapshot otherFresh otherHere otherLabel otherFrame =>
          have count := (snapshot.metadata.agreement secondStore.cells.length secondStore.trace
            otherSnapshot.metadata.present).1
          omega
      | copying progress otherFrame =>
          exact False.elim (fresh.not_has (.allocated job) (by simp [SnapshotCopy.Row.mentions]) progress.destinationAllocated)
      | complete otherToken completed otherHere otherLabel otherFrame =>
          exact False.elim (fresh.not_has (.allocated job) (by simp [SnapshotCopy.Row.mentions]) completed.destinationSnapshot.allocated)
  | @copying index remaining token progress frame =>
      cases second with
      | requested otherToken snapshot fresh otherHere otherLabel otherFrame =>
          exact False.elim (fresh.not_has (.allocated job) (by simp [SnapshotCopy.Row.mentions]) progress.destinationAllocated)
      | @copying otherIndex otherRemaining otherToken otherProgress otherFrame =>
          have same := progress.cursorUnique otherToken otherProgress.tokenPresent job source otherIndex otherRemaining
            otherProgress.tokenLabel
          have labels := congrArg SnapshotCopy.label same
          rw [otherProgress.tokenLabel,progress.tokenLabel] at labels
          exact congrArg (fun n => n+1) (SnapshotCopy.Row.cursor.inj labels).2.2.2.2.symm
      | complete otherToken completed otherHere otherLabel otherFrame =>
          exact False.elim (progress.notReplied completed.reply)
  | complete token completed here atToken frame =>
      cases second with
      | requested otherToken snapshot fresh otherHere otherLabel otherFrame =>
          exact False.elim (fresh.not_has (.reply job job) (by simp [SnapshotCopy.Row.mentions]) completed.reply)
      | copying progress otherFrame => exact False.elim (progress.notReplied completed.reply)
      | complete => rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedHeapFrames
