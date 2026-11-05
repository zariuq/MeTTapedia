import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineProjection

/-!
# Bounded published data and one physical protocol token

A running heap contains only stored data below its allocation frontier.
A waiting heap may additionally contain one specified request, cursor or
reply occurrence. The token is a physical occurrence, so duplicate labels
cannot hide replayable protocol resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedHeapFrames

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Suspension)

abbrev HeapRow := SnapshotCopy.Row Suspension
abbrev HeapOccurrence := SnapshotCopy.Occurrence Suspension
abbrev HeapWorld := SnapshotCopy.World Suspension

def DataBelow (bound : Nat) : HeapRow → Prop
  | .allocated name | .ready name | .metadata name _ _ | .cell name _ _ => name < bound
  | _ => False

theorem DataBelow.mono {first second : Nat} {row : HeapRow}
    (bounded : DataBelow first row) (le : first ≤ second) : DataBelow second row := by
  cases row <;> simp_all [DataBelow] <;> omega

theorem DataBelow.mentions {bound : Nat} {row : HeapRow} (bounded : DataBelow bound row) :
    ∀ name ∈ row.mentions, name < bound := by
  cases row <;> simp_all [DataBelow,SnapshotCopy.Row.mentions]

def Frame (bound : Nat) (token : Option HeapOccurrence) (present : Finset HeapOccurrence) : Prop :=
  ∀ occurrence ∈ present, DataBelow bound (SnapshotCopy.label occurrence) ∨ some occurrence = token

theorem Frame.mono {first second : Nat} {token : Option HeapOccurrence} {present : Finset HeapOccurrence}
    (frame : Frame first token present) (le : first ≤ second) : Frame second token present := by
  intro occurrence here
  exact (frame occurrence here).imp (fun bounded => bounded.mono le) id

theorem Frame.token_eq {bound : Nat} {token occurrence : HeapOccurrence} {present : Finset HeapOccurrence}
    (frame : Frame bound (some token) present) (here : occurrence ∈ present)
    (auxiliary : ¬ DataBelow bound (SnapshotCopy.label occurrence)) : occurrence = token := by
  rcases frame occurrence here with data | same
  · exact False.elim (auxiliary data)
  · exact Option.some.inj same

theorem Frame.not_has {bound : Nat} {present : Finset HeapOccurrence}
    (frame : Frame bound none present) (row : HeapRow) (auxiliary : ¬ DataBelow bound row) :
    ¬ SnapshotCopy.Has present row := by
  rintro ⟨occurrence,here,same⟩
  rcases frame occurrence here with data | impossible
  · exact auxiliary (same ▸ data)
  · cases impossible

theorem Frame.fresh {bound : Nat} {present : Finset HeapOccurrence}
    (frame : Frame bound none present) : SnapshotCopy.Fresh present bound := by
  intro occurrence here mentions
  rcases frame occurrence here with data | impossible
  · exact (Nat.lt_irrefl bound) (data.mentions bound mentions)
  · cases impossible

/-- A local resource proof for an actual selected firing. Old auxiliary
occurrences must be consumed, and each actual output must be data or the
new specified token. No successor configuration is supplied as a premise. -/
theorem Frame.after_selection {first second : Nat} {oldToken newToken : Option HeapOccurrence}
    {before : HeapWorld} {picked : Selection HeapOccurrence} {rule : RuleInstance HeapRow}
    (frame : Frame first oldToken before.present) (le : first ≤ second)
    (consumed : ∀ occurrence, some occurrence = oldToken → occurrence ∈ picked.taken)
    (made : ∀ occurrence ∈ picked.made,
      DataBelow second (SnapshotCopy.label occurrence) ∨ some occurrence = newToken) :
    Frame second newToken (picked.result SnapshotCopy.label rule before).present := by
  intro occurrence here
  rcases (NeedStoreOperations.Ground.present_iff occurrence).mp here with old | created
  · rcases frame occurrence old.1 with data | token
    · exact Or.inl (data.mono le)
    · exact False.elim (old.2 (consumed occurrence token))
  · exact made occurrence created

theorem Frame.after_firing {first second : Nat} {token : HeapOccurrence} {newToken : Option HeapOccurrence}
    {before after : HeapWorld} {rule : RuleInstance HeapRow}
    (frame : Frame first (some token) before.present) (le : first ≤ second)
    (firing : SnapshotCopy.Firing rule token before after)
    (made : ∀ occurrence ∈ firing.picked.made,
      DataBelow second (SnapshotCopy.label occurrence) ∨ some occurrence = newToken) :
    Frame second newToken after.present := by
  rw [firing.result]
  apply frame.after_selection le ?_ made
  intro occurrence same
  have equal := Option.some.inj same
  simp [firing.takes,equal]

theorem published_outputs_are_data (job : Nat) (event : NeedStoreOperations.Event)
    (row : HeapRow) (member : row ∈ (event.publishedRule job job).produce) : DataBelow (job+1) row := by
  cases event <;>
    simp only [NeedStoreOperations.Event.publishedRule,NeedStoreOperations.Event.rule,List.tail_cons,
      List.mem_cons,List.not_mem_nil,or_false] at member
  · rcases member with rfl | rfl <;> exact Nat.lt_succ_self job
  · subst row; exact Nat.lt_succ_self job
  · subst row; exact Nat.lt_succ_self job

/-- Final publication consumes the sole auxiliary reply. Every output is
bounded stored data, so the next running state has no protocol leftovers. -/
theorem Frame.after_publication {before after : HeapWorld} {job : Nat} {token : HeapOccurrence}
    (frame : Frame (job+1) (some token) before.present) (event : NeedStoreOperations.Event)
    (stepped : Step SnapshotCopy.action SnapshotCopy.label (event.publishedRule job job) before after) :
    Frame (job+1) none after.present := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  have replyTaken : SnapshotCopy.Row.reply job job ∈ (event.publishedRule job job).take := by
    cases event <;> simp [NeedStoreOperations.Event.publishedRule,NeedStoreOperations.Event.rule]
  rw [← (NeedStoreOperations.Ground.input_labels valid).1] at replyTaken
  obtain ⟨reply,selected,atReply⟩ := List.mem_map.mp replyTaken
  have replyHere := valid.occurrences.taken_subset (by simpa [Selection.commit] using selected)
  have replyEq := frame.token_eq replyHere (by simp [atReply,DataBelow])
  apply frame.after_selection (Nat.le_refl _) ?_ ?_
  · intro occurrence same
    have equal : occurrence = reply := (Option.some.inj same).trans replyEq.symm
    exact equal ▸ selected
  · intro occurrence made
    exact Or.inl (published_outputs_are_data job event _ (NeedStoreOperations.Ground.made_labels valid made))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedHeapFrames
